import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SelmerScaling.EpC
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SelmerScaling.BndOps
open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa

namespace UpperTheory.V.Pa

private theorem adicDD {A Γ : Type} [CommRing A] [TopologicalSpace Γ] {e : ℕ} (t : A) (d : Γ → DD A e)
    (h1 : AdicCont (Ideal.span {t}) fun g => (d g).a)
    (h2 : ∀ k, AdicCont (Ideal.span {t}) fun g => (d g).ep k)
    (h3 : ∀ k, AdicCont (Ideal.span {t}) fun g => (d g).ep' k)
    (h4 : AdicCont (Ideal.span {t}) fun g => (d g).eta) :
    AdicCont (Ideal.span {algebraMap A (DD A e) t}) d := by
  intro N
  rw [IsLocallyConstant.iff_eventually_eq]
  intro x
  have e1 := (h1 N).eventually_eq x
  have e2 := Filter.eventually_all.2 fun k => (h2 k N).eventually_eq x
  have e3 := Filter.eventually_all.2 fun k => (h3 k N).eventually_eq x
  have e4 := (h4 N).eventually_eq x
  filter_upwards [e1, e2, e3, e4] with y a1 a2 a3 a4
  simp only [Ideal.Quotient.eq, Ideal.span_singleton_pow, Ideal.mem_span_singleton'] at a1 a2 a3 a4 ⊢
  obtain ⟨b1, a1⟩ := a1
  obtain ⟨b4, a4⟩ := a4
  choose b2 a2 using a2
  choose b3 a3 using a3
  refine ⟨⟨b1, b2, b3, b4⟩, ?_⟩
  rw [← map_pow]
  have : algebraMap A (DD A e) (t ^ N) = DD.C (t ^ N) := rfl
  rw [this, sub_eq_add_neg]
  ext <;> simp [-map_pow, a1, a2, a3, a4, sub_eq_add_neg]

private theorem mapInj {X Y : Type} [CommRing X] [CommRing Y] {e : ℕ} (f : X →+* Y) (hf : Function.Injective f) :
    Function.Injective (DD.map (g := e) f) := by
  intro u v h
  have h1 := congrArg DD.a h
  have h2 := congrArg DD.ep h
  have h3 := congrArg DD.ep' h
  have h4 := congrArg DD.eta h
  ext k
  · exact hf h1
  · exact hf (congrFun h2 k)
  · exact hf (congrFun h3 k)
  · exact hf h4

private theorem selLift {l : ℕ} [Fact l.Prime] (F : GFrame l) {n : ℕ} {A R R' : Type} [CommRing A] [CommRing R] [CommRing R']
    [Algebra A R] [Algebra A R'] (t : A) (f : R →+* R') (hf : Function.Injective f)
    (ρ : F.G₀ → Matrix (Fin n) (Fin n) R) (w wi : F.Vl → Matrix (Fin n) (Fin n) R)
    (ρ' : F.G₀ → Matrix (Fin n) (Fin n) R') (w' wi' : F.Vl → Matrix (Fin n) (Fin n) R')
    (hρ : ∀ g, (ρ g).map f = ρ' g) (hw : ∀ g, (w g).map f = w' g) (hwi : ∀ g, (wi g).map f = wi' g)
    (V : Submodule A (Matrix (Fin n) (Fin n) R)) (V' : Submodule A (Matrix (Fin n) (Fin n) R'))
    (c : R') (hV : ∀ Z : Matrix (Fin n) (Fin n) R, ∀ Z' ∈ V', Z.map f = c • Z' → Z ∈ V)
    (z' : F.G₀ → Matrix (Fin n) (Fin n) R') (hz' : z' ∈ SelZ F t ρ' w' wi' V')
    (Y' : F.Vl → Matrix (Fin n) (Fin n) R') (hY' : ∀ v, Y' v ∈ V' ∧ LocAt F ρ' w' wi' z' v (Y' v))
    (z : F.G₀ → Matrix (Fin n) (Fin n) R) (hc : ∀ i j, AdicCont (Ideal.span {algebraMap A R t}) fun g => z g i j)
    (hz : ∀ g, (z g).map f = c • z' g) (Y : F.Vl → Matrix (Fin n) (Fin n) R) (hY : ∀ v, (Y v).map f = c • Y' v) :
    z ∈ SelZ F t ρ w wi V := by
  obtain ⟨h1, -, h3, h4, h5, -⟩ := hz'
  have inj : Function.Injective fun Z : Matrix (Fin n) (Fin n) R => Z.map f := Matrix.map_injective hf
  refine ⟨fun g => hV _ _ (h1 g) (hz g), hc, fun g g' => inj ?_, fun g => inj ?_, fun u g hg => inj ?_,
    fun v => ⟨Y v, hV _ _ (hY' v).1 (hY v), fun g => ?_⟩⟩
  · simp only [Matrix.map_add f (map_add f), Matrix.map_mul, hz, hρ, h3, smul_add, Matrix.mul_smul, Matrix.smul_mul]
  · simp only [Matrix.map_neg f (map_neg f), Matrix.transpose_map, hz, h4, smul_neg, Matrix.transpose_smul]
  · simp only [hz, h5 u g hg, smul_zero, Matrix.map_zero f (map_zero f)]
  · have key : (wi v * (z (F.φ v g) - dY F ρ (Y v) (F.φ v g)) * w v).map f =
        c • (wi' v * (z' (F.φ v g) - dY F ρ' (Y' v) (F.φ v g)) * w' v) := by
      simp only [dY, Matrix.map_sub f (map_sub f), Matrix.map_mul, hz, hρ, hw, hwi, hY, ← smul_sub, Matrix.mul_smul,
        Matrix.smul_mul]
    have k2 : ∀ i j, (wi' v * (z' (F.φ v g) - dY F ρ' (Y' v) (F.φ v g)) * w' v) i j = 0 →
        (wi v * (z (F.φ v g) - dY F ρ (Y v) (F.φ v g)) * w v) i j = 0 := by
      intro i j h0
      apply hf
      have := congrFun (congrFun key i) j
      rw [Matrix.map_apply, Matrix.smul_apply, h0, smul_zero] at this
      rw [this, map_zero]
    exact ⟨fun i j hij => k2 i j (((hY' v).2 g).1 i j hij), fun hg i => k2 i i (((hY' v).2 g).2 hg i)⟩

private theorem liftM {K Γ : Type} [Field K] [TopologicalSpace Γ] [Group Γ] [IsTopologicalGroup Γ] {n e : ℕ}
    (z : Γ → Matrix (Fin n) (Fin n) (DD (FractionRing (PowerSeries K)) e)) (hz : BndD (PowerSeries.X : PowerSeries K) z) :
    ∀ᶠ s : ℕ in Filter.atTop, ∃ z' : Γ → Matrix (Fin n) (Fin n) (DD (PowerSeries K) e),
      (∀ i j, AdicCont (Ideal.span {algebraMap (PowerSeries K) (DD (PowerSeries K) e) PowerSeries.X}) fun g => z' g i j) ∧
      ∀ g, (z' g).map (DD.map (algebraMap (PowerSeries K) (FractionRing (PowerSeries K)))) =
        (DD.C (algebraMap (PowerSeries K) (FractionRing (PowerSeries K)) PowerSeries.X ^ s) : DD (FractionRing (PowerSeries K)) e) • z g := by
  have B := fun φ hφ => Filter.eventually_atTop.2 ((bndOps K Γ).2.2.2.2 φ hφ)
  have e1 := Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun j => B _ (hz i j).1
  have e2 := Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun j =>
    Filter.eventually_all.2 fun k => B _ ((hz i j).2.1 k)
  have e3 := Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun j =>
    Filter.eventually_all.2 fun k => B _ ((hz i j).2.2.1 k)
  have e4 := Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun j => B _ (hz i j).2.2.2
  filter_upwards [e1, e2, e3, e4] with s a1 a2 a3 a4
  choose b1 c1 a1 using a1
  choose b2 c2 a2 using a2
  choose b3 c3 a3 using a3
  choose b4 c4 a4 using a4
  refine ⟨fun g => Matrix.of fun i j => ⟨b1 i j g, fun k => b2 i j k g, fun k => b3 i j k g, b4 i j g⟩,
    fun i j => adicDD _ _ (c1 i j) (c2 i j) (c3 i j) (c4 i j), fun g => ?_⟩
  ext i j <;> simp [-map_pow, DD.map, a1, a2, a3, a4]

end UpperTheory.V.Pa

theorem UpperTheory.V.Pa.selScale1 :
    ∀ (l : ℕ) [Fact l.Prime] (L : Loc) (G G0 : Glob l L) (h : G.Hom G0) (n : ℕ) (x : NP G0.frame n), ∀ (k : Kap x), ∀ z ∈ Sel1 h x.Fr k, BndD x.t z → ∃ s₀ : ℕ, ∀ s, s₀ ≤ s → ∃ z' ∈ Sel1 h x.A k, ∀ g, (z' g).map (DD.map (algebraMap x.A x.Fr)) = algebraMap x.A x.Fr x.t ^ s • z g := by
  intro l _ L G G0 h n x k z hz hb
  choose Y hY using hz.2.2.2.2.2
  have c0 := (bndOps x.K G.G₀).1
  have e1 := liftM z hb
  have e2 := Filter.eventually_all.2 fun v => liftM (K := x.K) (fun _ : G.G₀ => Y v)
    fun i j => ⟨c0 _, fun _ => c0 _, fun _ => c0 _, c0 _⟩
  apply Filter.eventually_atTop.1
  filter_upwards [e1, e2] with s a1 a2
  obtain ⟨z', hc, hz'⟩ := a1
  choose Y' _ hY' using a2
  have hf : Function.Injective (algebraMap x.A x.Fr) := IsFractionRing.injective _ _
  have m1 : ∀ M : Matrix (Fin n) (Fin n) x.A, (M.map (algebraMap x.A (DD x.A k.g))).map (DD.map (algebraMap x.A x.Fr)) =
      M.map (algebraMap x.A (DD x.Fr k.g)) := by
    intro M
    ext i j <;> first | rfl | exact map_zero (algebraMap x.A x.Fr)
  have m2 : ∀ Z : Fin k.g → Matrix (Fin n) (Fin n) x.A,
      (DD.epM fun j => (Z j).map (algebraMap x.A x.A)).map (DD.map (algebraMap x.A x.Fr)) =
      DD.epM fun j => (Z j).map (algebraMap x.A x.Fr) := by
    intro Z
    ext i j <;> first | rfl | exact map_zero (algebraMap x.A x.Fr)
  have m0 : (1 : Matrix (Fin n) (Fin n) (DD x.A k.g)).map (DD.map (algebraMap x.A x.Fr)) = 1 :=
    Matrix.map_one _ (map_zero _) (map_one _)
  have p : ∀ (b1 b2 b3 b4 : Bool) (u : DD x.A k.g), ∀ u' ∈ ddPart x.A x.Fr k.g b1 b2 b3 b4,
      DD.map (algebraMap x.A x.Fr) u = DD.C (algebraMap x.A x.Fr x.t ^ s) * u' → u ∈ ddPart x.A x.A k.g b1 b2 b3 b4 := by
    rintro b1 b2 b3 b4 u u' ⟨q1, q2, q3, q4⟩ hu
    refine ⟨fun e => hf ?_, fun e => funext fun j => hf ?_, fun e => funext fun j => hf ?_, fun e => hf ?_⟩
    · simpa [-map_pow, DD.map, q1 e] using congrArg DD.a hu
    · simpa [-map_pow, DD.map, q2 e] using congrFun (congrArg DD.ep hu) j
    · simpa [-map_pow, DD.map, q3 e] using congrFun (congrArg DD.ep' hu) j
    · simpa [-map_pow, DD.map, q4 e] using congrArg DD.eta hu
  refine ⟨z', selLift G.frame x.t (DD.map (algebraMap x.A x.Fr)) (mapInj _ hf) _ _ _ _ _ _ (fun g => ?_) (fun v => ?_) (fun v => ?_)
    _ _ (DD.C (algebraMap x.A x.Fr x.t ^ s)) (fun Z Z' hZ' hZ i j => ?_) z hz Y hY z' hc hz' (fun v => Y' v 1) (fun v => hY' v 1), hz'⟩
  · simp only [Kap.ρ1, NP.ρX, Matrix.map_mul, Matrix.map_add _ (map_add (DD.map (algebraMap x.A x.Fr))), m0, m1, m2]
  · simp only [Kap.w1, NP.wX, Matrix.map_mul, Matrix.map_sub _ (map_sub (DD.map (algebraMap x.A x.Fr))), m0, m1, m2]
  · simp only [Kap.wi1, NP.wiX, Matrix.map_mul, Matrix.map_add _ (map_add (DD.map (algebraMap x.A x.Fr))), m0, m1, m2]
  · have := congrFun (congrFun hZ i) j
    exact ⟨fun e => p _ _ _ _ _ _ ((hZ' i j).1 e) this, fun e => p _ _ _ _ _ _ ((hZ' i j).2 e) this⟩

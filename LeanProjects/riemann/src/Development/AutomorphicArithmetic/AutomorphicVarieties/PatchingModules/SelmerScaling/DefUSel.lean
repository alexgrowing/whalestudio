import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SelmerScaling.EpC
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SelmerScaling.LocLemma
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SelmerScaling.OddDiag
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SelmerScaling.HomBasic
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.SelmerScaling.BndOps
import Mathlib.Algebra.DualNumber
open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools UpperTheory.V.Pa

namespace UpperTheory.V.Pa

section SlopeTestRemainingChoices

variable {F R : Type} [CommRing F] [CommRing R] {n : ℕ}

private theorem mapd_mul (a : R →+* F) (d : R →+ F) (hd : ∀ y z, d (y * z) = a y * d z + d y * a z)
    (Y Z : Matrix (Fin n) (Fin n) R) : (Y * Z).map d = Y.map a * Z.map d + Y.map d * Z.map a := by
  ext i j
  simp only [map_apply, mul_apply, map_sum, hd, Finset.sum_add_distrib, Matrix.add_apply]

private def toDual (a : R →+* F) (d : R →+ F) (hd : ∀ y z, d (y * z) = a y * d z + d y * a z) (h1 : d 1 = 0) :
    R →+* DualNumber F where
  toFun y := TrivSqZeroExt.inl (a y) + TrivSqZeroExt.inr (d y)
  map_one' := by ext <;> simp [h1]
  map_zero' := by ext <;> simp
  map_add' y z := by ext <;> simp
  map_mul' y z := by ext <;> simp [hd, mul_comm]

private theorem toDual_fst (a : R →+* F) (d : R →+ F) (hd) (h1) (y : R) : (toDual a d hd h1 y).fst = a y := by
  simp [toDual]

private theorem toDual_snd (a : R →+* F) (d : R →+ F) (hd) (h1) (y : R) : (toDual a d hd h1 y).snd = d y := by
  simp [toDual]

private def evE (F : Type) [CommRing F] {n : ℕ} (p : Fin n → Prop) (b : Prop) :
    Subalgebra F (Matrix (Fin n) (Fin n) (DualNumber F)) where
  carrier := {Z | ∀ i j, (¬ (p i ↔ p j) → (Z i j).fst = 0) ∧ (((p i ↔ p j) ↔ b) → (Z i j).snd = 0)}
  mul_mem' := by
    intro Y Z hY hZ i j
    refine ⟨fun hij => ?_, fun hij => ?_⟩
    · rw [mul_apply, TrivSqZeroExt.fst_sum]
      refine Finset.sum_eq_zero fun k _ => ?_
      rw [TrivSqZeroExt.fst_mul]
      by_cases hk : p i ↔ p k
      · rw [(hZ k j).1 (by tauto), mul_zero]
      · rw [(hY i k).1 hk, zero_mul]
    · rw [mul_apply, TrivSqZeroExt.snd_sum]
      refine Finset.sum_eq_zero fun k _ => ?_
      rw [DualNumber.snd_mul]
      have e1 : (Y i k).fst * (Z k j).snd = 0 := by
        by_cases hk : p i ↔ p k
        · rw [(hZ k j).2 (by tauto), mul_zero]
        · rw [(hY i k).1 hk, zero_mul]
      have e2 : (Y i k).snd * (Z k j).fst = 0 := by
        by_cases hk : p k ↔ p j
        · rw [(hY i k).2 (by tauto), zero_mul]
        · rw [(hZ k j).1 hk, mul_zero]
      rw [e1, e2, add_zero]
  add_mem' := by
    intro Y Z hY hZ i j
    exact ⟨fun hij => by simp [(hY i j).1 hij, (hZ i j).1 hij], fun hij => by simp [(hY i j).2 hij, (hZ i j).2 hij]⟩
  algebraMap_mem' := by
    intro r i j
    rw [Matrix.algebraMap_matrix_apply]
    refine ⟨fun hij => ?_, fun _ => ?_⟩
    · rw [if_neg (by rintro rfl; exact hij Iff.rfl)]; rfl
    · split_ifs
      · simp [TrivSqZeroExt.algebraMap_eq_inl]
      · rfl

private theorem scal_mem (p : Fin n → Prop) (b : Prop) (y : DualNumber F) (hy : b → y.snd = 0) :
    algebraMap (DualNumber F) (Matrix (Fin n) (Fin n) (DualNumber F)) y ∈ evE F p b := by
  intro i j
  rw [Matrix.algebraMap_matrix_apply]
  refine ⟨fun hij => ?_, fun hij => ?_⟩
  · rw [if_neg (by rintro rfl; exact hij Iff.rfl)]; rfl
  · split_ifs with e
    · subst e
      exact hy (hij.1 Iff.rfl)
    · rfl

private theorem snd_l (A : Matrix (Fin n) (Fin n) F) (Z : Matrix (Fin n) (Fin n) (DualNumber F)) :
    (A.map (TrivSqZeroExt.inlHom F F) * Z).map TrivSqZeroExt.snd = A * Z.map TrivSqZeroExt.snd := by
  ext i j
  simp [mul_apply, TrivSqZeroExt.snd_sum]

private theorem snd_r (A : Matrix (Fin n) (Fin n) F) (Z : Matrix (Fin n) (Fin n) (DualNumber F)) :
    (Z * A.map (TrivSqZeroExt.inlHom F F)).map TrivSqZeroExt.snd = Z.map TrivSqZeroExt.snd * A := by
  ext i j
  simp [mul_apply, TrivSqZeroExt.snd_sum, mul_comm]

private theorem map_snd_sub (Y Z : Matrix (Fin n) (Fin n) (DualNumber F)) :
    (Y - Z).map TrivSqZeroExt.snd = Y.map TrivSqZeroExt.snd - Z.map TrivSqZeroExt.snd := by
  ext i j
  simp

private theorem snd_1 : (1 : Matrix (Fin n) (Fin n) (DualNumber F)).map TrivSqZeroExt.snd = 0 := by
  ext i j
  rw [map_apply, one_apply]
  split_ifs <;> simp

end SlopeTestRemainingChoices

private theorem locDual {F R H : Type} [Field F] [Infinite F] [CommRing R] [Group H] {n : ℕ}
    (a : R →+* F) (d : R →+ F) (hd : ∀ y z, d (y * z) = a y * d z + d y * a z) (h1 : d 1 = 0)
    (p : Fin n → Prop) (b : Prop)
    (U : H →* Matrix (Fin n) (Fin n) R) (ρ : H →* Matrix (Fin n) (Fin n) F) (χ : Fin n → H →* R) (ψ : Fin n → H →* F)
    (w wi : Matrix (Fin n) (Fin n) F) (hw : w * wi = 1) (hw' : wi * w = 1)
    (tri : ∀ g, (∀ i j, j < i → (wi * ρ g * w) i j = 0) ∧ ∀ i, (wi * ρ g * w) i i = ψ i g)
    (hU : ∀ g, (U g).map a = ρ g) (hχ : ∀ i g, a (χ i g) = ψ i g)
    (ne : ∀ i j, i ≠ j → ∃ g, ψ i g ≠ ψ j g)
    (ord : ∀ g : Fin n → H, (List.ofFn fun i => U (g i) - algebraMap R (Matrix (Fin n) (Fin n) R) (χ i (g i))).prod = 0)
    (hρ : ∀ g i j, ¬ (p i ↔ p j) → ρ g i j = 0) (hdU : ∀ g i j, ((p i ↔ p j) ↔ b) → d (U g i j) = 0)
    (hdχ : b → ∀ i g, d (χ i g) = 0) :
    ∃ Y : Matrix (Fin n) (Fin n) F, (∀ i j, ((p i ↔ p j) ↔ b) → Y i j = 0) ∧ ∀ g,
      (∀ i j, j < i → (wi * ((U g).map d * ρ g⁻¹ - (ρ g * Y * ρ g⁻¹ - Y)) * w) i j = 0) ∧
      ∀ i, χ i g = 1 → (wi * ((U g).map d * ρ g⁻¹ - (ρ g * Y * ρ g⁻¹ - Y)) * w) i i = 0 := by
  let π := toDual a d hd h1
  let ι : F →+* DualNumber F := TrivSqZeroExt.inlHom F F
  let e : DualNumber F →ₐ[F] F := TrivSqZeroExt.fstHom F F F
  have hUa : ∀ g i j, a (U g i j) = ρ g i j := fun g i j => by rw [← hU]; rfl
  obtain ⟨Y, hYE, -, hY⟩ := locLemma F (DualNumber F) H n e (RingHom.ker e) (evE F p b)
    (ι.mapMatrix.toMonoidHom.comp ρ) (π.mapMatrix.toMonoidHom.comp U) (fun i => ι.toMonoidHom.comp (ψ i))
    (fun i => π.toMonoidHom.comp (χ i)) (w.map ι) (wi.map ι)
    (fun y hy => ⟨2, by
      have : y.fst = 0 := hy
      ext <;> simp [pow_two, this]⟩)
    (by
      rw [eq_bot_iff, Ideal.mul_le]
      intro y hy z hz
      have h1 : y.fst = 0 := hy
      have h2 : z.fst = 0 := hz
      rw [Ideal.mem_bot]
      ext <;> simp [h1, h2])
    (by rw [← Matrix.map_mul, hw, Matrix.map_one _ (map_zero _) (map_one _)])
    (by rw [← Matrix.map_mul, hw', Matrix.map_one _ (map_zero _) (map_one _)])
    (fun g => by
      have : wi.map ι * (ι.mapMatrix.toMonoidHom.comp ρ) g * w.map ι = (wi * ρ g * w).map ι := by
        rw [Matrix.map_mul, Matrix.map_mul]; rfl
      rw [this]
      exact ⟨fun i j hij => by rw [map_apply, (tri g).1 i j hij, map_zero], fun i => by rw [map_apply, (tri g).2]; rfl⟩)
    (fun g i j => by
      show (π (U g i j) - ι (ρ g i j)).fst = 0
      rw [TrivSqZeroExt.fst_sub, toDual_fst, hUa]
      exact sub_self _)
    (fun i g => by
      show (π (χ i g) - ι (ψ i g)).fst = 0
      rw [TrivSqZeroExt.fst_sub, toDual_fst, hχ]
      exact sub_self _)
    ne
    (fun g => by
      have := congrArg π.mapMatrix (ord g)
      rw [map_zero, map_list_prod, List.map_ofFn] at this
      rw [← this]
      congr 2
      funext i
      simp only [Function.comp, map_sub]
      congr 1
      refine Matrix.ext fun r s => ?_
      simp only [RingHom.mapMatrix_apply, map_apply, Matrix.algebraMap_matrix_apply]
      split_ifs
      · rfl
      · exact (map_zero π).symm)
    (fun g => ⟨fun i j => ⟨fun hij => hρ g i j hij, fun _ => rfl⟩,
      fun i j => ⟨fun hij => (toDual_fst a d hd h1 _).trans ((hUa g i j).trans (hρ g i j hij)),
        fun hij => (toDual_snd a d hd h1 _).trans (hdU g i j hij)⟩⟩)
    (fun i g => ⟨scal_mem p b _ fun _ => rfl, scal_mem p b _ fun hb => (toDual_snd a d hd h1 _).trans (hdχ hb i g)⟩)
  refine ⟨Y.map TrivSqZeroExt.snd, fun i j hij => (hYE i j).2 hij, fun g => ?_⟩
  have hs : ((U g).map π).map TrivSqZeroExt.snd = (U g).map d := by
    ext i j
    exact toDual_snd a d hd h1 _
  have key : (wi.map ι * (((U g).map π * (ρ g⁻¹).map ι - 1) - ((ρ g).map ι * Y * (ρ g⁻¹).map ι - Y)) * w.map ι).map
      TrivSqZeroExt.snd =
      wi * ((U g).map d * ρ g⁻¹ - (ρ g * Y.map TrivSqZeroExt.snd * ρ g⁻¹ - Y.map TrivSqZeroExt.snd)) * w := by
    rw [snd_r, snd_l, map_snd_sub, map_snd_sub, map_snd_sub, snd_r, snd_r, snd_l, snd_1, hs, sub_zero]
  rw [← key]
  refine ⟨fun i j hij => congrArg TrivSqZeroExt.snd ((hY g).1 i j hij), fun i hi => ?_⟩
  have h2 := (hY g).2 i
  have h3 : ψ i g = 1 := by rw [← hχ, hi, map_one]
  have h4 : (ι.toMonoidHom.comp (ψ i)) g = 1 := by
    show ι (ψ i g) = 1
    rw [h3, map_one]
  have h5 : (π.toMonoidHom.comp (χ i)) g = 1 := by
    show π (χ i g) = 1
    rw [hi, map_one]
  simp only [h4, h5, mul_one, sub_self] at h2
  exact congrArg TrivSqZeroExt.snd h2

set_option maxHeartbeats 400000 in
private theorem selGen {l : ℕ} [Fact l.Prime] {L : Loc} {G G0 : Glob l L} (h : G.Hom G0) {n : ℕ} (x : NP G0.frame n)
    {e : ℕ} (u : G.G₀ → Matrix (Fin n) (Fin n) (DD x.Fr e)) (ψ : ∀ v, Fin n → L.Gv v →* (DD x.Fr e)ˣ)
    (hu : DefU h x u ψ) (d : DD x.Fr e →+ x.Fr) (hd : ∀ y z, d (y * z) = y.a * d z + d y * z.a)
    (hC : ∀ y : x.Fr, d (DD.C y) = 0) (b : Prop) (V : Submodule x.A (Matrix (Fin n) (Fin n) x.Fr))
    (hV : ∀ Z, Z ∈ V ↔ ∀ i j : Fin n, ((((i : ℕ) < x.a) ↔ ((j : ℕ) < x.a)) ↔ b) → Z i j = 0)
    (hdU : ∀ g (i j : Fin n), ((((i : ℕ) < x.a) ↔ ((j : ℕ) < x.a)) ↔ b) → d (u g i j) = 0)
    (hdχ : b → ∀ v i g, d (ψ v i g) = 0) (hb : ∀ i j, BndF x.t fun g => d (u g i j)) :
    (fun γ => (u γ).map d * x.ρX x.Fr (h.p₀ γ⁻¹)) ∈
      SelZ G.frame x.t (fun g => x.ρX x.Fr (h.p₀ g)) (x.wX x.Fr) (x.wiX x.Fr) V ∧
    BndM x.t (fun γ => (u γ).map d * x.ρX x.Fr (h.p₀ γ⁻¹)) := by
  obtain ⟨-, hcont, -, hφ, -, -⟩ := homBasic l L G G0 h
  let a : DD x.Fr e →+* x.Fr := (DD.aug x.Fr e).toRingHom
  have h1 : d 1 = 0 := hC 1
  let ρ : G.G₀ →* Matrix (Fin n) (Fin n) x.Fr :=
    (algebraMap x.A x.Fr).mapMatrix.toMonoidHom.comp ((mat x.ρ).comp h.p₀)
  have hρ : ∀ g, x.ρX x.Fr (h.p₀ g) = ρ g := fun _ => rfl
  have hred : ∀ g, (u g).map a = ρ g := hu.red
  have hρ0 : ∀ g (i j : Fin n), ¬ (((i : ℕ) < x.a) ↔ ((j : ℕ) < x.a)) → ρ g i j = 0 := fun g i j hij => by
    have : mat x.ρ (h.p₀ g) i j = 0 := (x.blk _ i j).2 hij
    show algebraMap x.A x.Fr (mat x.ρ (h.p₀ g) i j) = 0
    rw [this, map_zero]
  have hsc : ∀ c : x.Fr, ((DD.C c : DD x.Fr e) • (1 : Matrix (Fin n) (Fin n) (DD x.Fr e))).map d = 0 := fun c => by
    ext i j
    rw [map_apply, Matrix.smul_apply, one_apply]
    split_ifs
    · rw [smul_eq_mul, mul_one]; exact hC c
    · rw [smul_zero]; exact map_zero d
  have hinv : ∀ g, ρ g * ρ g⁻¹ = 1 := fun g => by rw [← map_mul, mul_inv_cancel, map_one]
  simp only [hρ]
  refine ⟨⟨fun g => ?_, fun i j N => ?_, fun g g' => ?_, fun g => ?_, fun w g hg => ?_, fun v => ?_⟩, fun i j => ?_⟩
  · rw [hV]
    intro i j hij
    show ((u g).map d * ρ g⁻¹) i j = 0
    rw [mul_apply]
    refine Finset.sum_eq_zero fun k _ => ?_
    by_cases hk : ((k : ℕ) < x.a) ↔ ((j : ℕ) < x.a)
    · rw [map_apply, hdU g i k (by tauto), zero_mul]
    · rw [hρ0 _ k j hk, mul_zero]
  · have ht : Ideal.span {algebraMap x.A x.Fr x.t} = ⊤ := by
      rw [Ideal.span_singleton_eq_top, isUnit_iff_ne_zero, Ne, IsFractionRing.to_map_eq_zero_iff]
      exact PowerSeries.X_ne_zero
    refine IsLocallyConstant.of_constant _ fun y z => Ideal.Quotient.eq.2 ?_
    rw [ht, Ideal.top_pow]
    trivial
  · show (u (g * g')).map d * ρ (g * g')⁻¹ = (u g).map d * ρ g⁻¹ + ρ g * ((u g').map d * ρ g'⁻¹) * ρ g⁻¹
    rw [hu.mul, mapd_mul a d hd, hred, hred, _root_.mul_inv_rev, map_mul, add_mul, add_comm]
    congr 1
    · rw [mul_assoc, ← mul_assoc (ρ g'), hinv, one_mul]
    · simp only [mul_assoc]
  · have hf := congrArg (fun Z => Matrix.map Z d) (hu.form g)
    rw [mapd_mul a d hd, transpose_map, transpose_map, hred, hred] at hf
    have hf' : (ρ g)ᵀ * (u (G.frame.conj g)).map d + ((u g).map d)ᵀ * ρ (G.frame.conj g) = 0 := hf.trans (hsc _)
    show (u (G.frame.conj g)).map d * ρ (G.frame.conj g)⁻¹ = -((u g).map d * ρ g⁻¹)ᵀ
    have e1 : (ρ g⁻¹)ᵀ * (ρ g)ᵀ = 1 := by rw [← transpose_mul, hinv, transpose_one]
    have e2 := congrArg (fun Z => (ρ g⁻¹)ᵀ * Z * ρ (G.frame.conj g)⁻¹) hf'
    simp only [mul_add, add_mul, mul_zero, zero_mul] at e2
    rw [← mul_assoc, e1, one_mul, mul_assoc, mul_assoc, hinv, mul_one] at e2
    rw [transpose_mul]
    exact eq_neg_of_add_eq_zero_left e2
  · show (u g).map d * ρ g⁻¹ = 0
    have := hsc 1
    rw [map_one, one_smul] at this
    rw [hu.ine w g hg, this, zero_mul]
  · obtain ⟨o1, o2, -, o3, -⟩ := oddDiag l L G G0 h n x x.Fr v
    haveI : Infinite x.A := Infinite.of_injective (fun m : ℕ => (PowerSeries.X : x.A) ^ m)
      (pow_injective_of_not_isUnit (by simp [PowerSeries.isUnit_iff_constantCoeff]) PowerSeries.X_ne_zero)
    haveI : Infinite x.Fr := Infinite.of_injective _ (IsFractionRing.injective x.A x.Fr)
    let U : G.G₀ →* Matrix (Fin n) (Fin n) (DD x.Fr e) := ⟨⟨u, hu.one⟩, hu.mul⟩
    obtain ⟨Y, hY0, hY⟩ := locDual a d hd h1 (fun i : Fin n => (i : ℕ) < x.a) b (U.comp (G.φ v)) (ρ.comp (G.φ v))
      (fun i => (Units.coeHom _).comp (ψ v i))
      (fun i => (algebraMap x.A x.Fr).toMonoidHom.comp ((Units.coeHom _).comp (x.ψ v i)))
      (x.wX x.Fr v) (x.wiX x.Fr v) o1 o2
      (fun g => by
        have := o3 g
        rw [← hφ] at this
        exact this)
      (fun g => hred _) (fun i g => hu.ψ_red v i g)
      (fun i j hij => by
        by_contra hh
        push Not at hh
        refine (x.N1 v).1 i j hij (MonoidHom.ext fun g => Units.ext ?_)
        exact IsFractionRing.injective x.A x.Fr (hh g))
      (hu.ord v) (fun g => hρ0 _) (fun g => hdU _) (fun hb i g => hdχ hb v i g)
    refine ⟨Y, (hV Y).2 hY0, fun g => ?_⟩
    have hg' := hY g
    have r1 : (ρ.comp (G.φ v)) g⁻¹ = ρ (G.φ v g)⁻¹ := by rw [MonoidHom.comp_apply, map_inv]
    rw [r1] at hg'
    refine ⟨hg'.1, fun hg i => hg'.2 i ?_⟩
    show ((ψ v i g : (DD x.Fr e)ˣ) : DD x.Fr e) = 1
    rw [hu.ψ_mu v i g hg, Units.val_one]
  · obtain ⟨-, b2, b3, b4, -⟩ := bndOps x.K G.G₀
    have hρb : ∀ r s, BndF x.t fun g => ρ g r s := fun r s => by
      refine b4 (fun g => mat x.ρ (h.p₀ g) r s) fun N => ?_
      have := (x.cont r s N).comp_continuous hcont
      rw [PowerSeries.maximalIdeal_eq_span_X] at this
      exact this
    simp only [mul_apply]
    exact b3 (Fin n) Finset.univ (fun k g => d (u g i k) * ρ g⁻¹ k j) fun k _ =>
      (b2 (fun g => d (u g i k)) (fun g => ρ g⁻¹ k j) (hb i k)
        (b2 (fun g => ρ g k j) (fun g => ρ g k j) (hρb k j) (hρb k j)).2.2.2).2.1

end UpperTheory.V.Pa

theorem UpperTheory.V.Pa.defUSel :
    ∀ (l : ℕ) [Fact l.Prime] (L : Loc) (G G0 : Glob l L) (h : G.Hom G0) (n : ℕ) (x : NP G0.frame n), ∀ (e : ℕ) (u : G.G₀ → Matrix (Fin n) (Fin n) (DD x.Fr e)) (ψ : ∀ v, Fin n → L.Gv v →* (DD x.Fr e)ˣ), DefU h x u ψ → ∀ k, (epC' h x u k ∈ SelP h x x.Fr ∧ BndM x.t (epC' h x u k)) ∧ epC h x u k ∈ SelM h x x.Fr ∧ BndM x.t (epC h x u k) := by
  intro l _ L G G0 h n x e u ψ hu k
  refine ⟨?_, ?_⟩
  · refine selGen h x u ψ hu ⟨⟨fun y => y.ep' k, rfl⟩, fun _ _ => rfl⟩ (fun _ _ => rfl) (fun _ => rfl) False _
      (fun Z => ⟨fun hZ i j hij => (hZ i j).2 hij.1, fun hZ i j => ⟨fun _ => trivial, fun hij => hZ i j (iff_false_intro hij)⟩⟩)
      (fun g i j hij => ?_) (fun hb => hb.elim) (fun i j => (hu.bnd i j).2.2.1 k)
    exact congrFun (((hu.even g i j).2 hij.1).2.2.1 rfl) k
  · refine selGen h x u ψ hu ⟨⟨fun y => y.ep k, rfl⟩, fun _ _ => rfl⟩ (fun _ _ => rfl) (fun _ => rfl) True _
      (fun Z => ⟨fun hZ i j hij => (hZ i j).1 (hij.2 trivial), fun hZ i j => ⟨fun hij => hZ i j (iff_true_intro hij), fun _ => trivial⟩⟩)
      (fun g i j hij => ?_) (fun _ v i g => ?_) (fun i j => (hu.bnd i j).2.1 k)
    · exact congrFun (((hu.even g i j).1 (hij.2 trivial)).2.1 rfl) k
    · exact congrFun ((hu.ψ_even v i g).2.1 rfl) k

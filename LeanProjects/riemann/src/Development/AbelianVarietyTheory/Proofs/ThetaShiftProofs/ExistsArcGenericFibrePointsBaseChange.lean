import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HasArcDataIff
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsFShiftZeroIff
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.MemRangeCompIffOfIsClosedImmersion
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.FormalThetaSumShiftPeriodDiv
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.IsExtensionPullOver

noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArcPts
open scoped CategoryTheory.Obj LaurentSeries PowerSeries

namespace GlobalTheory.ArcBaseChange

open GlobalTheory.FieldBaseChange GlobalTheory.Points

section Values

variable {K F : Type} [Field K] [Field F] {X Y Y' Z : Scheme.{0}}

theorem le_spMap_iff (f : K →+* F) (x : Sp K ⟶ X) (U : X.Opens) : ⊤ ≤ (spMap f ≫ x) ⁻¹ᵁ U ↔ ⊤ ≤ x ⁻¹ᵁ U := by
  refine ⟨fun h z _ => ?_, fun h z _ => h (Set.mem_univ (spMap f z))⟩
  have e : z = spMap f (IsLocalRing.closedPoint F) := Subsingleton.elim (α := PrimeSpectrum K) _ _
  rw [e]
  exact h (Set.mem_univ (IsLocalRing.closedPoint F))

theorem valR_spMap_field (f : K →+* F) (x : Sp K ⟶ X) (U : X.Opens) (a : Γ(X, U)) :
    valR (spMap f ≫ x) U a = f (valR x U a) := by
  by_cases h : ⊤ ≤ x ⁻¹ᵁ U
  · exact valR_spMap_comp f x U h a
  · rw [valR, valR, dif_neg h, dif_neg (mt (le_spMap_iff f x U).1 h), map_zero]

theorem le_wchart {R : Type} [CommRing R] {L : LB Z} {q : Y ⟶ Z} {x : Sp R ⟶ Y} {j : L.ι}
    (h : ⊤ ≤ (x ≫ q) ⁻¹ᵁ L.U j) : ⊤ ≤ x ⁻¹ᵁ LB.wchart L (fun _ : Fin 1 => q) (fun _ => j) :=
  fun _ hz => Set.mem_iInter.2 fun _ => h hz

abbrev SecM {R : Type} [CommRing R] (π : Y ⟶ Sp R) (L : LB Z) (q : Y ⟶ Z) (m : ℕ) : Type :=
  SecOver π (LB.LinComb L (K := Fin 1) (fun _ => q) (fun _ => (m : ℤ)))

def evalAt {R : Type} [CommRing R] (π : Y ⟶ Sp R) {L : LB Z} {q : Y ⟶ Z} (m : ℕ) (x : Sp R ⟶ Y)
    (hx : x ≫ π = 𝟙 _) (j : L.ι) (h : ⊤ ≤ (x ≫ q) ⁻¹ᵁ L.U j) : SecM π L q m →ₗ[R] R where
  toFun s := ArcPts.sval (show SecP L q m from s) x j
  map_add' s t := valR_add x _ (le_wchart h) _ _
  map_smul' c s := by
    refine (valR_mul x _ (le_wchart h) _ _).trans (congrArg (· * _) ?_)
    refine (valR_res x le_top (le_wchart h) _).trans ?_
    refine (valR_comp x π ⊤ _).symm.trans ?_
    rw [hx, ← Spec.map_id]
    exact valR_specMap (𝟙 _) c

variable {π : Y ⟶ Sp K} {π' : Y' ⟶ Sp F} {f : K →+* F} {p : Y' ⟶ Y} (hp : p ≫ π = π' ≫ spMap f)
  {L : LB Z} {q : Y ⟶ Z} {q' : Y' ⟶ Z} (hq : q' = p ≫ q)

abbrev pullM (m : ℕ) : SecM π L q m →ₛₗ[f] SecM π' L q' m :=
  pullOver L (fun _ : Fin 1 => (m : ℤ)) hp (fun _ => hq)

theorem sval_pullM (m : ℕ) (s : SecM π L q m) (x : Sp K ⟶ Y) (x' : Sp F ⟶ Y') (hx : x' ≫ p = spMap f ≫ x)
    (j : L.ι) (h : ⊤ ≤ (x' ≫ q') ⁻¹ᵁ L.U j) :
    ArcPts.sval (show SecP L q' m from pullM hp hq m s) x' j = f (ArcPts.sval (show SecP L q m from s) x j) := by
  refine (valR_res x' (wchart_eq (fun _ => hq) (fun _ => j)).le (le_wchart h) _).trans ?_
  refine (valR_comp x' p _ _).symm.trans ?_
  rw [hx]
  exact valR_spMap_field f x _ _

end Values

section Fibre

variable {K F : Type} [Field K] [Field F] {S : Scheme.{0}} (G : Over S) (y : Sp K ⟶ S) (f : K →+* F)

def toSmall : Over.mk (spMap f ≫ y) ⟶ Over.mk y := Over.homMk (spMap f) rfl

def fibMap : pullback G.hom (spMap f ≫ y) ⟶ pullback G.hom y :=
  pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ spMap f) (by rw [pullback.condition, Category.assoc])

theorem fibMap_fst : pullback.fst G.hom (spMap f ≫ y) = fibMap G y f ≫ pullback.fst G.hom y :=
  (pullback.lift_fst _ _ _).symm

theorem fibMap_snd : fibMap G y f ≫ pullback.snd G.hom y = pullback.snd G.hom (spMap f ≫ y) ≫ spMap f :=
  pullback.lift_snd _ _ _

theorem isPullback_fibMap :
    IsPullback (fibMap G y f) (pullback.snd G.hom (spMap f ≫ y)) (pullback.snd G.hom y) (spMap f) :=
  IsPullback.of_right (by rw [← fibMap_fst]; exact IsPullback.of_hasPullback _ _) (fibMap_snd G y f)
    (IsPullback.of_hasPullback G.hom y)

variable {G y}

theorem fib_fst (x : Over.mk y ⟶ G) : fib x ≫ pullback.fst _ _ = x.left := pullback.lift_fst _ _ _

theorem fib_snd (x : Over.mk y ⟶ G) : fib x ≫ pullback.snd _ _ = 𝟙 _ := pullback.lift_snd _ _ _

theorem fib_fibMap (x : Over.mk y ⟶ G) : fib (toSmall y f ≫ x) ≫ fibMap G y f = spMap f ≫ fib x := by
  apply pullback.hom_ext
  · rw [Category.assoc, ← fibMap_fst, fib_fst, Category.assoc, fib_fst]; rfl
  · rw [Category.assoc, fibMap_snd, ← Category.assoc, fib_snd, Category.assoc, fib_snd, Category.id_comp,
      Category.comp_id]

abbrev pullFib (L : LB G.left) (m : ℕ) : SecM (pullback.snd G.hom y) L (pullback.fst G.hom y) m →ₛₗ[f]
    SecM (pullback.snd G.hom (spMap f ≫ y)) L (pullback.fst G.hom (spMap f ≫ y)) m :=
  pullM (fibMap_snd G y f) (fibMap_fst G y f) m

theorem chart_iff (L : LB G.left) (x : Over.mk y ⟶ G) (j : L.ι) :
    ⊤ ≤ (fib (toSmall y f ≫ x) ≫ pullback.fst _ _) ⁻¹ᵁ L.U j ↔ ⊤ ≤ (fib x ≫ pullback.fst _ _) ⁻¹ᵁ L.U j := by
  rw [fib_fst, fib_fst]
  exact le_spMap_iff f x.left _

theorem sval_pullFib {L : LB G.left} {m : ℕ} (s : SecP L (pullback.fst G.hom y) m) (x : Over.mk y ⟶ G) (j : L.ι)
    (h : ⊤ ≤ (fib (toSmall y f ≫ x) ≫ pullback.fst _ _) ⁻¹ᵁ L.U j) :
    ArcPts.sval (show SecP L _ m from pullFib f L m s) (fib (toSmall y f ≫ x)) j = f (ArcPts.sval s (fib x) j) :=
  sval_pullM _ _ m s _ _ (fib_fibMap f x) j h

theorem hasVal_pullFib {L : LB G.left} {m : ℕ} {s : SecP L (pullback.fst G.hom y) m} {x : Over.mk y ⟶ G}
    {τ : L.ι → K} {r : K} (h : HasVal s (fib x) τ r) :
    HasVal (show SecP L _ m from pullFib f L m s) (fib (toSmall y f ≫ x)) (fun j => f (τ j)) (f r) := fun j hj => by
  rw [sval_pullFib f s x j hj, h j ((chart_iff f L x j).1 hj), map_mul, map_pow]

theorem noetherianSpace_fibre [GrpObj G] (hG : IsSemiAbelian G) :
    TopologicalSpace.NoetherianSpace (pullback G.hom y : Scheme) := by
  have := hG.smooth
  have := hG.quasiCompact
  have : IsLocallyNoetherian (pullback G.hom y : Scheme) :=
    LocallyOfFiniteType.isLocallyNoetherian (pullback.snd G.hom y)
  have : CompactSpace (pullback G.hom y : Scheme) :=
    QuasiCompact.compactSpace_of_compactSpace (pullback.snd G.hom y)
  have : IsNoetherian (pullback G.hom y : Scheme) := {}
  infer_instance

end Fibre

section Ext

variable {K F : Type} [Field K] [Field F] [Algebra K F] {S : Scheme.{0}} {G : Over S} [GrpObj G] {y : Sp K ⟶ S}
  {L : LB G.left}

theorem isExtension_pullFib (hG : IsSemiAbelian G) (hL : L.IsLB) (m : ℕ) :
    IsExtension (pullFib (y := y) (algebraMap K F) L m) := by
  have := noetherianSpace_fibre (y := y) hG
  exact isExtension_pullOver (isPullback_fibMap G y (algebraMap K F)) hL _ _

theorem sep_ext (hG : IsSemiAbelian G) (hL : L.IsLB) {m : ℕ} {V : Type} (x : V → (Over.mk y ⟶ G))
    (τ : V → L.ι → K) (τ' : V → L.ι → F)
    (h : ∀ s : SecP L (pullback.fst G.hom y) m, (∀ v, HasVal s (fib (x v)) (τ v) 0) → ∀ i, s.f i = 0)
    (s : SecP L (pullback.fst G.hom (spMap (algebraMap K F) ≫ y)) m)
    (hs : ∀ v, HasVal s (fib (toSmall y (algebraMap K F) ≫ x v)) (τ' v) 0) (i) : s.f i = 0 := by
  have hE := isExtension_pullFib (F := F) (y := y) hG hL m
  have e : (show SecM (pullback.snd G.hom (spMap (algebraMap K F) ≫ y)) L _ m from s) = 0 := by
    refine hE.eq_of_coord fun ℓ Λ hΛ => ?_
    rw [map_zero]
    refine SecOver.ext _ _ (h _ fun v j hj => ?_)
    have hj' := (chart_iff (algebraMap K F) L (x v) j).2 hj
    have := IsCoord.natural (a' := (algebraMap K F).toSemilinearMap) hE.span hΛ (Λ' := ℓ.toAddMonoidHom)
      (fun c v => by
        show ℓ (c * algebraMap K F v) = ℓ c * v
        rw [mul_comm, ← Algebra.smul_def, map_smul, smul_eq_mul, mul_comm])
      (evalAt _ m _ (fib_snd (x v)) j hj) (evalAt _ m _ (fib_snd _) j hj')
      (fun t => sval_pullFib _ t (x v) j hj') s
    refine this.symm.trans ?_
    refine (congrArg ℓ (hs v j hj')).trans ?_
    rw [zero_mul, zero_mul, map_zero]
  exact congrArg (fun t : SecP L _ m => t.f i) e

theorem span_ext (hG : IsSemiAbelian G) (hL : L.IsLB) {m : ℕ} {V I : Type} (x : V → (Over.mk y ⟶ G))
    (τ : V → L.ι → K) (φ : I → V → K)
    (h : ∀ s : SecP L (pullback.fst G.hom y) m, ∃ (n : ℕ) (r : Fin n → K) (i : Fin n → I),
      ∀ v, HasVal s (fib (x v)) (τ v) (∑ a, r a * φ (i a) v))
    (s : SecP L (pullback.fst G.hom (spMap (algebraMap K F) ≫ y)) m) :
    ∃ (n : ℕ) (r : Fin n → F) (i : Fin n → I), ∀ v, HasVal s (fib (toSmall y (algebraMap K F) ≫ x v))
      (fun j => algebraMap K F (τ v j)) (∑ a, r a * algebraMap K F (φ (i a) v)) := by
  obtain ⟨N, c, t, e⟩ := (isExtension_pullFib (F := F) (y := y) hG hL m).exists_sum s
  choose n r i hr using fun b => h (t b)
  let ρ := (Fintype.equivFin (Σ b, Fin (n b))).symm
  refine ⟨_, fun a => c (ρ a).1 * algebraMap K F (r _ (ρ a).2), fun a => i _ (ρ a).2, fun v j hj => ?_⟩
  rw [ρ.sum_comp (fun a => c a.1 * algebraMap K F (r _ a.2) * algebraMap K F (φ (i _ a.2) v)), Fintype.sum_sigma,
    Finset.sum_mul]
  refine (congrArg (evalAt _ m _ (fib_snd _) j hj) e).trans ?_
  rw [map_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [map_smul, smul_eq_mul]
  refine (congrArg (c b * ·) (hasVal_pullFib _ (hr b v) j hj)).trans ?_
  simp only [map_sum, map_mul, ← _root_.mul_assoc, Finset.mul_sum]

end Ext

section Theta

variable {O : Type} [CommRing O] [StarRing O] (A : AnArc O)

theorem eq_of_isFShift (k : ℕ) [NeZero k] (α : A.X) (th : (Fin A.gB → ℂ) → ℂ) (la : A.La) (z : A.V) (F : ℂ⸨X⸩)
    (h : IsFShift A k α th la z F) : F = A.FSumShift k α th la z := by
  refine HahnSeries.ext (funext fun n => (h.2 n).trans ?_)
  rw [AnArc.coeff_FSumShift]
  refine finsum_cond_eq_sum_of_cond_iff _ fun {m} _ => ?_
  rw [AnArc.mem_level, eq_sub_iff_add_eq]

theorem exists_theta_ne_zero (h : AnFin A) (k : ℕ) [NeZero k] : ∃ th ∈ A.Theta k 0, th ≠ 0 := by
  obtain ⟨th, hth, h0⟩ := h.2
  obtain ⟨z, hz⟩ := Function.ne_iff.1 h0
  have key : ∀ n : ℕ, th ^ (n + 1) ∈ A.Theta (n + 1) 0 := fun n => by
    induction n with
    | zero => simpa using hth
    | succ n ih => simpa [pow_succ] using A.mul_mem_Theta ih hth
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (NeZero.ne k)
  exact ⟨_, key n, Function.ne_iff.2 ⟨z, pow_ne_zero _ hz⟩⟩

end Theta

theorem exists_fpts_baseChange : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)] (S : Scheme.{0}) (A : AnArc (𝓞 E)) (t : SAB H S) (y : Sp ℂ⸨X⸩ ⟶ S) (Φ : GenPts A t y) (F : Type) [Field F] (f : ℂ⸨X⸩ →+* F) (φ : ∀ j, (Σ α : A.X, A.Theta j α) → A.V → F), AnFin A → (∀ (j : ℕ) [NeZero j] i v, φ j i v = f (A.FSum j i.1 i.2 v)) → ∃ Θ : FPts (I := fun j => Σ α : A.X, A.Theta j α) (fun e v => A.actV e v) t (spMap f ≫ y) φ, (∀ v, (Θ.x v).left = spMap f ≫ (Φ.x v).left ∧ ∀ j, ⊤ ≤ (Φ.x v).left ⁻¹ᵁ t.PP.L.U j → Θ.τ v j = f (Φ.τ v j)) ∧ ∀ (k : ℕ) [NeZero k] (ξ : 𝟙_ (Over S) ⟶ t.G) (la : A.La) (ψ : (Σ α : A.X, A.Theta k α) → A.V → ℂ⸨X⸩), Φ.LevelPt k (toUnit _ ≫ ξ) la → (∀ i z, IsFShift A k i.1 i.2 la z (ψ i z)) → Θ.Lev k (toUnit _ ≫ ξ) (fun i z => f (ψ i z)) := by
  intro E _ _ _ H _ S A t y Φ F _ f φ hA hφ
  let _ : Algebra ℂ⸨X⸩ F := f.toAlgebra
  have hc : ∀ v j, ⊤ ≤ (toSmall y f ≫ Φ.x v).left ⁻¹ᵁ t.PP.L.U j → ⊤ ≤ (Φ.x v).left ⁻¹ᵁ t.PP.L.U j :=
    fun v j => (le_spMap_iff f (Φ.x v).left _).1
  let Θ : FPts (I := fun j => Σ α : A.X, A.Theta j α) (fun e v => A.actV e v) t (spMap f ≫ y) φ :=
    { x := fun v => toSmall y f ≫ Φ.x v
      add := fun v v' => by rw [Φ.add, MonObj.comp_mul]
      lin := fun e v => by rw [Φ.lin, Category.assoc]
      τ := fun v j => f (Φ.τ v j)
      frm := fun v => ⟨fun j hj => ((Φ.frm v).1 j (hc v j hj)).map f, fun j j' hj => by
        beta_reduce
        rw [(Φ.frm v).2 j j' ((le_spMap_iff f (Φ.x v).left _).1 hj), map_mul, ← valR_spMap_field]
        rfl⟩
      rig := fun j hj => by rw [Φ.rig j (hc 0 j hj), valR_spMap_field]
      sig := fun j i => pullFib f t.PP.L j (Φ.sig j i.1 i.2)
      val := fun j hj i v => by
        have : NeZero j := ⟨by omega⟩
        rw [hφ]
        exact hasVal_pullFib f (Φ.val j i.1 i.2 i.2.2 v)
      span := fun j hj s => by
        have : NeZero j := ⟨by omega⟩
        simp only [hφ]
        refine span_ext t.semi t.PP.isLB Φ.x Φ.τ (fun (i : Σ α : A.X, A.Theta j α) v => A.FSum j i.1 i.2 v)
          (fun s => ?_) s
        obtain ⟨g, ⟨n, r, α, th, h₁, h₂⟩, hg⟩ := Φ.span j s
        exact ⟨n, r, fun a => ⟨α a, th a, (h₁ a).2⟩, fun v => h₂ v ▸ hg v⟩
      sep := fun j hj s hs => by
        have : NeZero j := ⟨by omega⟩
        exact sep_ext t.semi t.PP.isLB Φ.x Φ.τ _ (Φ.sep j) s hs }
  refine ⟨Θ, fun v => ⟨rfl, fun _ _ => rfl⟩, fun k _ ξ la ψ hp hψ => ?_⟩
  have hξ : toUnit (Over.mk (spMap f ≫ y)) ≫ ξ = toSmall y f ≫ toUnit _ ≫ ξ := by
    rw [← Category.assoc, comp_toUnit]
  refine ⟨?_, ?_, fun i i' z j hj => ?_⟩
  · rw [hξ, ← MonObj.comp_pow, hp.1, MonObj.comp_one]
  · obtain ⟨th, hth, h0⟩ := exists_theta_ne_zero A hA k
    refine ⟨NeZero.ne k, ⟨0, th, hth⟩, ⟨0 + la.y, _, A.shift_mem_Theta hth la⟩, fun z hz => ?_, ?_⟩
    · rw [hφ, map_ne_zero] at hz
      rw [map_ne_zero, eq_of_isFShift A k _ _ la z _ (hψ _ z),
        A.FSumShift_eq k la (Int.mul_ediv_cancel' (hp.dvd _)).symm]
      exact mul_ne_zero (HahnSeries.single_ne_zero (Complex.exp_ne_zero _)) hz
    · obtain ⟨z, hz⟩ := A.exists_FSum_ne_zero k (0 + la.y) (th := A.shift k la 0 th)
        fun h => h0 (A.shift_injective k la 0 (h.trans (map_zero _).symm))
      exact ⟨z, by rw [hφ, map_ne_zero]; exact hz⟩
  · have e : Θ.x z * (toUnit (Over.mk (spMap f ≫ y)) ≫ ξ) = toSmall y f ≫ (Φ.x z * (toUnit _ ≫ ξ)) := by
      rw [hξ, MonObj.comp_mul]
    rw [e] at hj ⊢
    have hj' : ⊤ ≤ (fib (toSmall y f ≫ (Φ.x z * (toUnit _ ≫ ξ))) ≫ pullback.fst _ _) ⁻¹ᵁ t.PP.L.U j := by
      rw [fib_fst]; exact hj
    have := congrArg f (hp.2.2 i.1 i'.1 i.2 i.2.2 i'.2 i'.2.2 z _ _ j (hψ i z) (hψ i' z)
      ((le_spMap_iff f _ _).1 hj))
    rw [map_mul, map_mul, ← sval_pullFib f _ _ j hj', ← sval_pullFib f _ _ j hj'] at this
    exact this

end GlobalTheory.ArcBaseChange

import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HasArcDataIff
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IdealPart
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.IsAdicCompleteIdealEps
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.SvalEqSumOfHasVal

noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArcPts
open scoped CategoryTheory.Obj LaurentSeries PowerSeries
open GlobalTheory.ConstTan

namespace GlobalTheory.GenericTan

section Charts

variable {R : Type} [CommRing R] [IsLocalRing R] {Z Z' : Scheme.{0}} {L : LB Z}

theorem valR_cocycle (hL : L.IsLB) (x : Sp R ⟶ Z) {i j k : L.ι} (hi : ⊤ ≤ x ⁻¹ᵁ L.U i) (hj : ⊤ ≤ x ⁻¹ᵁ L.U j)
    (hk : ⊤ ≤ x ⁻¹ᵁ L.U k) :
    valR x (L.U i ⊓ L.U j) (L.g i j).val * valR x (L.U j ⊓ L.U k) (L.g j k).val =
      valR x (L.U i ⊓ L.U k) (L.g i k).val := by
  apply toStkA_injective
  rw [map_mul, toStkA_valR x (L.U i ⊓ L.U j) _ (fun _ hz => ⟨hi hz, hj hz⟩),
    toStkA_valR x (L.U j ⊓ L.U k) _ (fun _ hz => ⟨hj hz, hk hz⟩),
    toStkA_valR x (L.U i ⊓ L.U k) _ (fun _ hz => ⟨hi hz, hk hz⟩), ← Units.val_mul,
    gm_cocycle hL x _ (hi trivial) (hj trivial) (hk trivial)]

theorem valR_self (hL : L.IsLB) (x : Sp R ⟶ Z) {j : L.ι} (h : ⊤ ≤ x ⁻¹ᵁ L.U j) :
    valR x (L.U j ⊓ L.U j) (L.g j j).val = 1 := by
  apply toStkA_injective
  rw [toStkA_valR x (L.U j ⊓ L.U j) _ (fun _ hz => ⟨h hz, h hz⟩), map_one]
  exact congrArg Units.val (gm_self hL x _ (h trivial))

theorem isFrm_spread (hL : L.IsLB) (x : Sp R ⟶ Z) {k : L.ι} (hk : ⊤ ≤ x ⁻¹ᵁ L.U k) {a : R} (ha : IsUnit a) :
    IsFrm L x (fun j => valR x (L.U j ⊓ L.U k) (L.g j k).val * a) := by
  refine ⟨fun j hj => (FormalValue.isUnit_valR x (L.U j ⊓ L.U k) (fun _ hz => ⟨hj hz, hk hz⟩) _).mul ha,
    fun j j' h => ?_⟩
  rw [← _root_.mul_assoc, valR_cocycle hL x (fun _ hz => (h hz).1) (fun _ hz => (h hz).2) hk]

theorem sval_chart {p : Z' ⟶ Z} {m : ℕ} (s : SecP L p m) (q : Sp R ⟶ Z') {j k : L.ι}
    (hj : ⊤ ≤ (q ≫ p) ⁻¹ᵁ L.U j) (hk : ⊤ ≤ (q ≫ p) ⁻¹ᵁ L.U k) :
    ArcPts.sval s q j = valR (q ≫ p) (L.U j ⊓ L.U k) (L.g j k).val ^ m * ArcPts.sval s q k := by
  have wj : ⊤ ≤ q ⁻¹ᵁ LB.wchart L (fun _ : Fin 1 => p) (fun _ => j) :=
    fun z hz => Set.mem_iInter.2 fun _ => hj hz
  have wk : ⊤ ≤ q ⁻¹ᵁ LB.wchart L (fun _ : Fin 1 => p) (fun _ => k) :=
    fun z hz => Set.mem_iInter.2 fun _ => hk hz
  apply toStkA_injective
  rw [map_mul, map_pow, toStkA_valR (q ≫ p) (L.U j ⊓ L.U k) _ (fun _ hz => ⟨hj hz, hk hz⟩)]
  refine (FormalValue.toStkA_valR_eq_gs q _ _ wj _).trans ((sec_trans s q _ (wj trivial) (wk trivial)).trans
    (congrArg₂ (· * ·) ?_ (FormalValue.toStkA_valR_eq_gs q _ _ wk _).symm))
  rw [trF, Fin.prod_univ_one, zpow_natCast, Units.val_pow_eq_pow_val]

theorem hasVal_of_chart {p : Z' ⟶ Z} {m : ℕ} (s : SecP L p m) (q : Sp R ⟶ Z') {τ : L.ι → R}
    (hτ : IsFrm L (q ≫ p) τ) {k : L.ι} (hk : ⊤ ≤ (q ≫ p) ⁻¹ᵁ L.U k) {r : R}
    (h : ArcPts.sval s q k = r * τ k ^ m) : HasVal s q τ r := fun j hj => by
  rw [sval_chart s q hj hk, h, hτ.2 j k (fun _ hz => ⟨hj hz, hk hz⟩), mul_pow, mul_left_comm]

def pullPow (p : Z' ⟶ Z) {m : ℕ} (σ : Out.H0 L m) : SecP L p m :=
  have l : ∀ j : Fin 1 → L.ι, LB.wchart L (fun _ : Fin 1 => p) j ≤ p ⁻¹ᵁ LB.wchart L (fun _ : Fin 1 => 𝟙 Z) j :=
    fun _ _ hy => Set.mem_iInter.2 fun k => Set.mem_iInter.1 hy k
  { f := fun j => (p.appLE _ _ (l j)).hom (σ.f j)
    compat := fun (j j' : Fin 1 → L.ι) => fn_ext fun y hy => by
      have v : ∀ j : Fin 1 → L.ι, y ∈ LB.wchart L (fun _ : Fin 1 => p) j →
          gs (𝟙 Z') y _ ((p.appLE _ _ (l j)).hom (σ.f j)) =
          gs (𝟙 Z' ≫ p) y (LB.wchart L (fun _ : Fin 1 => 𝟙 Z) j) (σ.f j) := fun j hj =>
        (gs_res (𝟙 Z') y (l j) hj _).trans (gs_pull _ p y _ (l j hj) _)
      refine ((gs_res (𝟙 Z') y _ hy _).trans (v j hy.1)).trans (Eq.trans ?_ ((gs_mul (𝟙 Z') y _ hy _ _).trans
        (congrArg₂ (· * ·) ((gs_unit (𝟙 Z') y _ hy _).trans
          (congrArg Units.val (gm_linComb L _ _ (𝟙 Z') y j j' hy.1 hy.2)))
          ((gs_res (𝟙 Z') y _ hy _).trans (v j' hy.2)))).symm)
      rw [sec_trans σ (𝟙 Z' ≫ p) y (l j hy.1) (l j' hy.2)]
      simp only [trF, Category.comp_id] }

omit [IsLocalRing R] in
theorem sval_pullPow (p : Z' ⟶ Z) {m : ℕ} (σ : Out.H0 L m) (q : Sp R ⟶ Z') {k : L.ι}
    (hk : ⊤ ≤ (q ≫ p) ⁻¹ᵁ L.U k) : ArcPts.sval (pullPow p σ) q k =
      valR (q ≫ p) (LB.wchart L (fun _ : Fin 1 => 𝟙 Z) (fun _ => k)) (σ.f (fun _ => k)) :=
  HolHom.valR_appLE q p _ _ _ _ (fun z hz => Set.mem_iInter.2 fun _ => hk hz)

omit [IsLocalRing R] in
theorem le_powChart {x : Sp R ⟶ Z} {k : L.ι} (hk : ⊤ ≤ x ⁻¹ᵁ L.U k) :
    ⊤ ≤ x ⁻¹ᵁ LB.wchart L (fun _ : Fin 1 => 𝟙 Z) (fun _ => k) :=
  fun _ hz => Set.mem_iInter.2 fun _ => hk hz

end Charts

theorem isTan_of_sections : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) [StarRing (𝓞 E)] (A : AnArc (𝓞 E)) (t : SAB H (Sp ℂ⟦X⟧)) (Φ : GenPts A t gen) (L : RigLB t.G) (x : A.V → (Sp ℂ⟦X⟧ ⟶ t.G.left)) (τ : A.V → L.L.ι → ℂ⟦X⟧) (z : A.V) (v : Sp (DualNumber ℂ⟦X⟧) ⟶ t.G.left) (k₀ : L.L.ι) (τ₁ : DualNumber ℂ⟦X⟧) (ρ : DualNumber ℂ⟦X⟧ →+* DualNumber ℂ⸨X⸩) (νK : Sp (DualNumber ℂ⸨X⸩) ⟶ pullback t.G.hom gen), L = t.PP → (∀ u, (Φ.x u).left = gen ≫ x u ∧ ∀ (k : L.L.ι) (k' : t.PP.L.ι), HEq k k' → ⊤ ≤ x u ⁻¹ᵁ L.L.U k → Φ.τ u k' = algebraMap ℂ⟦X⟧ ℂ⸨X⸩ (τ u k)) → spMap (TrivSqZeroExt.fstHom ℂ⟦X⟧ ℂ⟦X⟧ ℂ⟦X⟧).toRingHom ≫ v = x 0 → ⊤ ≤ v ⁻¹ᵁ L.L.U k₀ → IsUnit τ₁ → (∀ r, ρ (TrivSqZeroExt.inl r) = TrivSqZeroExt.inl (algebraMap ℂ⟦X⟧ ℂ⸨X⸩ r)) → ρ DualNumber.eps = DualNumber.eps → νK ≫ pullback.fst _ _ = spMap ρ ≫ v → νK ≫ pullback.snd _ _ = spMap (algebraMap ℂ⸨X⸩ (DualNumber ℂ⸨X⸩)) → (∀ (j : ℕ) [NeZero j] (α : A.X), ∀ th ∈ A.Theta j α, ∀ F, IsDFSum A j α th z F → ∃ (m : ℕ) (σ : Out.H0 L.L j), (∀ u k, ⊤ ≤ x u ⁻¹ᵁ L.L.U k → algebraMap ℂ⟦X⟧ ℂ⸨X⸩ (valR (x u) (LB.wchart L.L (fun _ : Fin 1 => 𝟙 t.G.left) (fun _ => k)) (σ.f (fun _ => k))) = HahnSeries.single (m : ℤ) (1 : ℂ) * A.FSum j α th u * algebraMap ℂ⟦X⟧ ℂ⸨X⸩ (τ u k) ^ j) ∧ ρ (valR v (LB.wchart L.L (fun _ : Fin 1 => 𝟙 t.G.left) (fun _ => k₀)) (σ.f (fun _ => k₀))) = TrivSqZeroExt.inl (HahnSeries.single (m : ℤ) (1 : ℂ)) * (TrivSqZeroExt.inl (A.FSum j α th 0) + TrivSqZeroExt.inr F) * ρ τ₁ ^ j) → Φ.IsTan z νK := by
  intro E _ _ _ H _ A t Φ L x τ z v k₀ τ₁ ρ νK hL hx hv hk₀ hτ₁ hρ hε hfst hsnd hsec
  subst hL
  have hρ' := eq_dualMapR _ ρ hρ hε
  have hK : ⊤ ≤ (νK ≫ pullback.fst _ _) ⁻¹ᵁ t.PP.L.U k₀ := by
    rw [hfst]; exact FormalValue.top_le_comp hk₀ _
  haveI := isLocalRing_dual ℂ⸨X⸩
  have hfrm := isFrm_spread t.PP.isLB (νK ≫ pullback.fst _ _) hK (hτ₁.map ρ)
  refine ⟨hsnd, ?_, _, hfrm, fun j _ α th hth F hF => ?_⟩
  · refine pullback.hom_ext ?_ ?_
    · rw [Category.assoc, hfst, fib, pullback.lift_fst, (hx 0).1, ← hv, ← Category.assoc, ← Category.assoc,
        ← Spec.map_comp, ← Spec.map_comp]
      congr 2
      ext1
      refine RingHom.ext fun a => ?_
      rw [hρ']
      exact fst_dualMapR _ a
    · rw [Category.assoc, hsnd, fib, pullback.lift_snd, ← Spec.map_comp, ← Spec.map_id]
      congr 1
  · obtain ⟨m, σ, h₁, h₂⟩ := hsec j α th hth F hF
    have key := sval_eq_sum_of_hasVal E H _ A t gen Φ j (pullPow (pullback.fst t.G.hom gen) σ) 1
      (fun _ => HahnSeries.single (m : ℤ) (1 : ℂ)) (fun _ => α) (fun _ => th) (fun _ => hth) (fun u => by
        have e : fib (Φ.x u) ≫ pullback.fst t.G.hom gen = gen ≫ x u := by
          rw [fib, pullback.lift_fst, (hx u).1]
        obtain ⟨k, hk⟩ := exists_chart t.PP.isLB (x u (cpt ℂ⟦X⟧))
        have hk' := (top_le_iff_cpt _ _).2 hk
        have hk'' : ⊤ ≤ (fib (Φ.x u) ≫ pullback.fst t.G.hom gen) ⁻¹ᵁ t.PP.L.U k := by
          rw [e]; exact FormalValue.top_le_comp hk' _
        refine hasVal_of_chart _ _ ?_ hk'' ?_
        · rw [e, ← (hx u).1]; exact Φ.frm u
        · rw [sval_pullPow _ _ _ hk'', e, Fin.sum_univ_one, (hx u).2 k k HEq.rfl hk', ← h₁ u k hk']
          exact FormalValue.valR_spMap _ _ _ (le_powChart hk') _)
      _ _ νK hsnd k₀ hK
    refine hasVal_of_chart _ _ hfrm hK ?_
    rw [sval_pullPow _ _ _ hK, hfst, Fin.sum_univ_one, TrivSqZeroExt.algebraMap_eq_inl] at key
    replace key := (h₂.symm.trans (FormalValue.valR_spMap ρ v _ (le_powChart hk₀) _).symm).trans key
    rw [_root_.mul_assoc] at key
    have hu : IsUnit (TrivSqZeroExt.inl (HahnSeries.single (m : ℤ) (1 : ℂ)) : DualNumber ℂ⸨X⸩) :=
      TrivSqZeroExt.isUnit_iff_isUnit_fst.2 (Ne.isUnit (by simp))
    rw [valR_self t.PP.isLB _ hK, _root_.one_mul]
    exact (hu.mul_left_cancel key).symm

end GlobalTheory.GenericTan

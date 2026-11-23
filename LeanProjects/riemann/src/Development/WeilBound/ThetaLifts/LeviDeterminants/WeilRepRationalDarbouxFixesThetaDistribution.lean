import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AutomorphicSpectrum.Proofs.MembershipProofs.ThetaSumTensorProductStatement
import Development.WeilBound.ThetaLifts.LeviDeterminants.EqZeroOfTheta

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Matrix TensorProduct

noncomputable section
namespace PositivityTheory.ThKF0.Resc

section Gen

variable {R : Type} [CommRing R] {K : Type} [CommRing K] [Algebra R K] {c : K →ₐ[R] K}
  {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]

theorem ug_smul {v : K} (hv : IsUnit v) (J : Matrix β β K) : UG c (v • J) = UG c J := by
  ext g
  change (g : Matrix β β K)ᵀ * (v • J) * (g : Matrix β β K).map c = v • J ↔
    (g : Matrix β β K)ᵀ * J * (g : Matrix β β K).map c = J
  rw [Matrix.mul_smul, Matrix.smul_mul]
  exact hv.smul_left_cancel

omit [Fintype β] [DecidableEq β] in
theorem dbl_smul (v : K) (J : Matrix β β K) : dbl (v • J) = v • dbl J := by
  ext (i | i) (j | j) <;> simp [dbl]

omit [DecidableEq α] [DecidableEq β] in
theorem symp_smul {ξ ξ' u v : K} (h : ξ = ξ' * u * v) (JA : Matrix α α K) (JB : Matrix β β K) (x y : Matrix α β K) :
    symp c ξ' (u • JA) (v • JB) x y = symp c ξ JA JB x y := by
  rw [symp, symp, h]
  congr 1
  simp only [hTens, Finset.mul_sum, Matrix.smul_apply, smul_eq_mul]
  refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
    Finset.sum_congr rfl fun _ _ => by ring

variable [Invertible (2 : R)]

theorem isWeilB_resc {ξ ξ' u v : K} (h : ξ = ξ' * u * v) (hv : IsUnit v) {JA JA' : Matrix α α K} {JB JB' : Matrix β β K}
    (hA : JA' = u • JA) (hB : JB' = v • JB) {κ : Type} [Fintype κ] {C : TestClass R} {ψ : AddChar R ℂ}
    {d : Darboux (symp c ξ JA JB) κ} {χ : Kˣ →* Circle} {om : UG c JB →* Module.End ℂ ((κ → R) → ℂ)}
    (hW : IsWeilB c C ψ ξ JA JB d χ om) :
    ∃ (d' : Darboux (symp c ξ' JA' JB') κ) (om' : UG c JB' →* Module.End ℂ ((κ → R) → ℂ)), d'.e = d.e ∧
      IsWeilB c C ψ ξ' JA' JB' d' χ om' ∧ ∀ g : UG c JB, ∃ g' : UG c JB', g'.1 = g.1 ∧ om' g' = om g := by
  subst hA hB
  obtain ⟨hS, dd, omd, hdd, hSd, hR, hbox⟩ := hW
  have hU : UG c (v • JB) = UG c JB := ug_smul hv JB
  have hUd : UG c (dbl (v • JB)) = UG c (dbl JB) := by rw [dbl_smul]; exact ug_smul hv _
  refine ⟨⟨d.e, fun w w' => (symp_smul h JA JB w w').trans (d.form w w')⟩, om.comp (Subgroup.inclusion hU.le), rfl,
    ⟨⟨fun g => hS.pres _, fun g => hS.impl (Subgroup.inclusion hU.le g), fun g => hS.adm _⟩,
      ⟨dd.e, fun w w' => by rw [dbl_smul]; exact (symp_smul h JA _ w w').trans (dd.form w w')⟩,
      omd.comp (Subgroup.inclusion hUd.le), hdd,
      ⟨fun g => hSd.pres _, fun g => hSd.impl (Subgroup.inclusion hUd.le g), fun g => hSd.adm _⟩,
      fun l hl hinv p t hp => hR l hl hinv (Subgroup.inclusion hUd.le p) t hp,
      fun g gd hg => hbox (Subgroup.inclusion hU.le g) (Subgroup.inclusion hUd.le gd) hg⟩,
    fun g => ⟨Subgroup.inclusion hU.ge g, rfl, rfl⟩⟩

end Gen

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem exists_isQuad (hσ : IsCMExt F E σ) : ∃ δ : E, IsQuad σ δ := by
  obtain ⟨-, hc, h2, hτ⟩ := hσ
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  have hi : ∀ x, σ (σ x) = x := fun x => τ.injective (by rw [hτ, hτ, star_star])
  obtain ⟨x, hx⟩ : ∃ x, σ x ≠ x := by
    by_contra h
    push Not at h
    refine IsTotallyComplex.complexEmbedding_not_isReal τ (ComplexEmbedding.isReal_iff.2 (RingHom.ext fun x => ?_))
    have := hτ τ x
    rw [h] at this
    exact this.symm
  have h0 : x - σ x ≠ 0 := sub_ne_zero.2 hx.symm
  have ha : σ (x - σ x) = -(x - σ x) := by rw [map_sub, hi, neg_sub]
  have hl : LinearIndependent F ![(1 : E), x - σ x] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    have h1 := congrArg σ hst
    have h4 := hst
    rw [Algebra.smul_def, Algebra.smul_def] at h1 h4
    rw [map_add, map_mul, map_mul, σ.commutes, σ.commutes, map_one, ha, map_zero] at h1
    have h3 : algebraMap F E (s + s) = 0 := by
      rw [map_add]
      linear_combination h4 + h1
    have hs : s = 0 := add_self_eq_zero.1 ((map_eq_zero _).1 h3)
    rw [hs, zero_smul, zero_add] at hst
    exact ⟨hs, (smul_eq_zero.1 hst).resolve_right h0⟩
  refine ⟨x - σ x, h0.isUnit, ha, basisOfLinearIndependentOfCardEqFinrank hl (by simp [h2]), ?_, ?_⟩ <;>
    simp

theorem exists_ratCoord (h2 : Module.finrank F E = 2) {α β κ : Type} [Fintype α] [Fintype β] [Fintype κ]
    (hκ : Fintype.card κ = Fintype.card α * Fintype.card β)
    (e : Matrix α β (AE F E) ≃ₗ[AF F] (κ → AF F) × (κ → AF F))
    (he : ∀ x : Matrix α β E, ∃ y z : κ → F,
      e (incM F x) = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i))) :
    ∃ d₀ : Matrix α β E ≃ₗ[F] (κ → F) × (κ → F), ∀ x,
      e (incM F x) = (fun i => algebraMap F (AF F) ((d₀ x).1 i), fun i => algebraMap F (AF F) ((d₀ x).2 i)) := by
  choose y z h using he
  have inj := AdeleRing.algebraMap_injective (𝓞 F) F
  have hadd : ∀ a b : Matrix α β E, incM F (a + b) = incM F a + incM F b := fun a b => by
    ext i j; simp [incM]
  have hsm : ∀ (t : F) (a : Matrix α β E), incM F (t • a) = algebraMap F (AF F) t • incM F a := fun t a => by
    ext i j
    change (1 : AF F) ⊗ₜ[F] (t • a i j) = algebraMap F (AF F) t • ((1 : AF F) ⊗ₜ[F] a i j)
    rw [algebraMap_smul, TensorProduct.tmul_smul]
  let f : Matrix α β E →ₗ[F] (κ → F) × (κ → F) :=
    { toFun := fun x => (y x, z x)
      map_add' := fun a b => by
        have := h (a + b)
        rw [hadd, map_add, h, h] at this
        refine Prod.ext (funext fun i => inj ?_) (funext fun i => inj ?_)
        · simpa using (congrFun (congrArg Prod.fst this) i).symm
        · simpa using (congrFun (congrArg Prod.snd this) i).symm
      map_smul' := fun t a => by
        have := h (t • a)
        rw [hsm, map_smul, h] at this
        refine Prod.ext (funext fun i => inj ?_) (funext fun i => inj ?_)
        · exact (congrFun (congrArg Prod.fst this) i).symm.trans (map_mul (algebraMap F (AF F)) t (y a i)).symm
        · exact (congrFun (congrArg Prod.snd this) i).symm.trans (map_mul (algebraMap F (AF F)) t (z a i)).symm }
  have hf : Function.Injective f := fun a b hab => by
    have h1 : y a = y b := congrArg Prod.fst hab
    have h3 : z a = z b := congrArg Prod.snd hab
    have : incM F a = incM F b := e.injective (by rw [h, h, h1, h3])
    exact Matrix.map_injective (Algebra.TensorProduct.includeRight_injective inj) this
  have : Module.Finite F E := Module.finite_of_finrank_eq_succ h2
  refine ⟨f.linearEquivOfInjective hf ?_, h⟩
  rw [Module.finrank_matrix, h2, Module.finrank_prod, Module.finrank_fintype_fun_eq_card, hκ]
  ring

theorem member (hσ : IsCMExt F E σ) {ψ : AddChar (AF F) ℂ} (hψ : IsStd ψ) {δ a b : E} (hq : IsQuad σ δ)
    (hab : -1 = δ * a * b) {α β κ : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype κ]
    (hκ : Fintype.card κ = Fintype.card α * Fintype.card β) {JA : Matrix α α E} {JB : Matrix β β E}
    (hA : IsHerm σ (a • JA)) (hB : IsHerm σ (b • JB))
    {d : Darboux (symp (R := AF F) (cA σ) (-1) (incM F JA) (incM F JB)) κ}
    (hd : ∀ x : Matrix α β E, ∃ y z : κ → F,
      d.e (incM F x) = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i)))
    {χ : Chr F E} (hχ : IsHecke F E χ) {om : UG (cA σ) (incM F JB) →* Module.End ℂ ((κ → AF F) → ℂ)}
    (h : IsWeilB (cA σ) (adeleClass F) ψ (-1) (incM F JA) (incM F JB) d χ om)
    (g : UG (cA σ) (incM F JB)) (γ : Matrix β β E) (hg : (g.1 : Matrix β β (AE F E)) = incM F γ) :
    ∀ Φ ∈ schA F κ, thetaSum F (om g Φ) = thetaSum F Φ := by
  have hb : b ≠ 0 := by
    rintro rfl
    simp at hab
  have hsm : ∀ {ι : Type} (t : E) (J : Matrix ι ι E), incM F (t • J) = inclR (F := F) (AF F) t • incM F J := fun t J => by
    ext i j; simp [incM]
  obtain ⟨d', om', he, hW, hom⟩ := isWeilB_resc (ξ' := inclR (F := F) (AF F) δ)
    (by rw [← map_mul, ← map_mul, ← hab, map_neg, map_one]) (hb.isUnit.map (inclR (F := F) (AF F))) (hsm a JA) (hsm b JB) h
  obtain ⟨d₀, hd₀⟩ := exists_ratCoord hσ.2.2.1 hκ d.e hd
  obtain ⟨g', hg', e⟩ := hom g
  rw [← e]
  refine GlobalTheory.T.seesaw_theta_dual_pair F E σ δ α β κ (a • JA) (b • JB) ψ hψ.1 (isStd_ne_one hψ) hψ.2.1 hq hA hB d' d₀
    (fun x => by rw [← hd₀, ← he]; rfl) χ om' (fun z u hu => ?_) hW g' ⟨γ, by rw [hg']; exact hg⟩
  have : Nontrivial (AF F) := (AdeleRing.algebraMap_injective (𝓞 F) F).nontrivial
  have : Nontrivial (AF F ⊗[F] E) := (Algebra.TensorProduct.includeRight_injective (A := AF F) (B := E)
    (algebraMap F (AF F)).injective).nontrivial
  have hz : z ≠ 0 := by
    rintro rfl
    exact u.ne_zero (by rw [hu, TensorProduct.tmul_zero])
  rw [show u = Units.map (inclR (F := F) (AF F)).toMonoidHom (Units.mk0 z hz) from Units.ext hu]
  exact hχ.2 _

omit [NumberField E] in
theorem rat_mat {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {γ : UA σ J} (hγ : γ ∈ ratU σ J) :
    ∃ γ₀ : Matrix (Fin n) (Fin n) E, (γ.1 : Matrix (Fin n) (Fin n) (AE F E)) = incM F γ₀ := by
  obtain ⟨g₀, hg₀⟩ := Subgroup.mem_subgroupOf.mp hγ
  exact ⟨g₀, by rw [← hg₀]; rfl⟩

end PositivityTheory.ThKF0.Resc

namespace PositivityTheory.ThKF0

open Resc

theorem darboux_coordinates_rational_exist : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (ψ : AddChar (AF F) ℂ), IsStd ψ → ∀ (n d : ℕ) (JX : Matrix (Fin n) (Fin n) E) (JW : Matrix (Fin d) (Fin d) E), (∀ i j, σ (JX j i) = JX i j) → JX.det ≠ 0 → (∀ i j, σ (JW j i) = -JW i j) → JW.det ≠ 0 → ∀ (co : Darboux (symp (R := AF F) (cA σ) (-1) (incM F JX) (incM F JW)) (Fin n × Fin d)), (∀ x : Matrix (Fin n) (Fin d) E, ∃ y z : Fin n × Fin d → F, co.e (incM F x) = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i))) → ∀ χX χW : Chr F E, IsHecke F E χX → IsHecke F E χW → ∀ om : UA σ JX × UA σ JW →* Module.End ℂ ((Fin n × Fin d → AF F) → ℂ), IsUWeilPair (cA σ) (adeleClass F) ψ (-1) (incM F JX) (incM F JW) co χX χW om → ∀ γ ∈ ratU σ JX, ∀ γ' ∈ ratU σ JW, ∀ Φ ∈ schA F (Fin n × Fin d), thetaSum F (om (γ, γ') Φ) = thetaSum F Φ := by
  intro F E _ _ _ _ _ σ hσ ψ hψ n d JX JW hX hXd hW hWd co hco χX χW hχX hχW om hom γ hγ γ' hγ' Φ hΦ
  obtain ⟨hB, d', hd', hA⟩ := hom.isWeilPair
  obtain ⟨g₀, hg₀⟩ := rat_mat hγ
  obtain ⟨g₀', hg₀'⟩ := rat_mat hγ'
  obtain ⟨δ, hq⟩ := exists_isQuad hσ
  have h0 : δ ≠ 0 := hq.unit.ne_zero
  have eX : IsHerm σ ((1 : E) • JX) := by rw [one_smul]; exact ⟨hX, hXd.isUnit⟩
  have eW : IsHerm σ ((-δ⁻¹) • JW) := by
    refine ⟨fun i j => by simp [hW i j, hq.anti], Ne.isUnit ?_⟩
    rw [Matrix.det_smul]
    exact mul_ne_zero (pow_ne_zero _ (neg_ne_zero.2 (inv_ne_zero h0))) hWd
  have hco' : ∀ x : Matrix (Fin d) (Fin n) E, ∃ y z : Fin n × Fin d → F,
      d'.e (incM F x) = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i)) := fun x => by
    have e : incM F x = (incM F xᵀ)ᵀ := rfl
    rw [e, hd']
    exact hco xᵀ
  have e : om (γ, γ') Φ = om.comp (MonoidHom.inl _ _) γ (om.comp (MonoidHom.inr _ _) γ' Φ) := by
    rw [← Module.End.mul_apply, MonoidHom.comp_apply, MonoidHom.comp_apply, ← map_mul]
    simp
  rw [e, member hσ hψ hq (by field_simp) (by simp [Nat.mul_comm]) eW eX hco' hχW hA γ g₀ hg₀ _ (hB.1.pres γ' Φ hΦ)]
  exact member hσ hψ hq (by field_simp) (by simp) eX eW hco hχX hB γ' g₀' hg₀' Φ hΦ

end PositivityTheory.ThKF0

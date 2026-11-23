import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DivPowerCompatTwoFormDerivativeCompOneForm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLiftAndAugmentationMap
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPdPoly
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsDPMorphismOfIsStd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FilProperties
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FilIsSubDPIdeal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuotientSubDPIdeal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsStdStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DividedPowerFiltrationIdealLeMapOfIsDPMorphismStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PoincareLemmaTruncatedDivPowerPolyOneVariableStatement

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
  GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.CxCoh GlobalTheory.PDA GlobalTheory.PDForm GlobalTheory.SmoothLift

namespace GlobalTheory.PDForm.FreeThick

theorem ringHom_eq_of_basis {B C : Type} [CommRing B] [CommRing C] (Q : PDPoly B) {f g : Q.P →+* C}
    (h1 : ∀ b, f (algebraMap B Q.P b) = g (algebraMap B Q.P b)) (h2 : ∀ k, f (Q.e k) = g (Q.e k)) : f = g := by
  ext p
  have hp : p ∈ Submodule.span B (Set.range Q.e) := Q.e.mem_span p
  induction hp using Submodule.span_induction with
  | mem x hx => obtain ⟨k, rfl⟩ := hx; exact h2 k
  | zero => simp
  | add x y _ _ hx hy => rw [map_add, map_add, hx, hy]
  | smul b x _ hx => rw [Algebra.smul_def, map_mul, map_mul, hx, h1]

end GlobalTheory.PDForm.FreeThick

namespace GlobalTheory.PDForm

open GlobalTheory.PDForm.FreeThick in

theorem exists_isFree_one_qAt : ∀ (R : Type) [CommRing R] (I : Ideal R) (κ : DividedPowers I) (X : Scheme.{0})
    (t : X ⟶ Sp R) (n : ℕ) (T : Thick κ t), IsLev T.δ (n + 1) → ∃ (F : Thick κ t) (u : T ⟶ F) (τ : Unit → F.B),
      IsFree (n + 1) u τ ∧ (KK κ t).QAt u := by
  intro R _ I κ X t n T hT
  obtain ⟨Q⟩ := GlobalTheory.exists_pdPoly T.B
  obtain ⟨η, hη⟩ := GlobalTheory.T.exists_dividedPowers_ext_isStd T.B T.J T.δ Q
  obtain ⟨hlift, ε, hε⟩ := GlobalTheory.PDA.PDPoly.exists_lift_and_aug T.B Q
  have hfil := GlobalTheory.PDA.fil_properties Q.P (Q.ext T.J) η
  obtain ⟨K, hK⟩ : ∃ K : Ideal Q.P, K = fil η (n + 1) := ⟨_, rfl⟩
  have hsub : η.IsSubDPIdeal K := by rw [hK]; exact GlobalTheory.PDA.fil_isSubDPIdeal Q.P (Q.ext T.J) η (n + 1) (by omega)
  obtain ⟨δ', hδ', huniv⟩ := (GlobalTheory.DPQuot.quotient_subDPIdeal Q.P (Q.ext T.J) η).1 K hsub
  have hKle : K ≤ Q.ext T.J := by rw [hK]; exact (hfil.2.2.1 1 (n + 1) (by omega)).trans hfil.2.1.le
  letI : Algebra R Q.P := ((algebraMap T.B Q.P).comp (algebraMap R T.B)).toAlgebra
  haveI : IsScalarTower R T.B Q.P := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  have hε1 : ∀ b, ε (algebraMap T.B Q.P b) = b := fun b ↦ by simp
  have hεJ : ∀ p : Q.P, ε p ∈ T.J ↔ p ∈ Q.ext T.J := by
    intro p
    constructor
    · intro hp
      have : p = algebraMap T.B Q.P (ε p) + (p - algebraMap T.B Q.P (ε p)) := by ring
      rw [this]
      refine add_mem (Q.algebraMap_mem_ext hp) (Ideal.mem_sup_right ((hε _).2 ?_))
      rw [map_sub, hε1, sub_self]
    · intro hp
      have hle : Q.ext T.J ≤ T.J.comap (ε : Q.P →+* T.B) := by
        refine sup_le (Ideal.map_le_iff_le_comap.2 fun b hb ↦ ?_) fun q hq ↦ ?_
        · rw [Ideal.mem_comap]; change ε (algebraMap T.B Q.P b) ∈ T.J; rw [hε1]; exact hb
        · rw [Ideal.mem_comap]; change ε q ∈ T.J; rw [(hε q).1 hq]; exact T.J.zero_mem
      exact hle hp
  let π₀ : Q.P →+* T.B₀ := T.π.comp (ε : Q.P →+* T.B)
  have hπ₀ : ∀ p, π₀ p = 0 ↔ p ∈ Q.ext T.J := fun p ↦ (T.ker _).trans (hεJ p)
  let πF : Q.P ⧸ K →+* T.B₀ := Ideal.Quotient.lift K π₀ fun p hp ↦ (hπ₀ p).2 (hKle hp)
  have hπF : ∀ p, πF (Ideal.Quotient.mk K p) = T.π (ε p) := fun p ↦ rfl
  have hlev : IsLev δ' (n + 1) := by
    have h := GlobalTheory.T.dividedPowerFiltrationIdeal_le_map_of_isDPMorphism Q.P (Q.ext T.J) η (Q.P ⧸ K) _ δ' (Ideal.Quotient.mk K) hδ' rfl (n + 1)
    rw [← hK, Ideal.map_quotient_self] at h
    exact le_bot_iff.1 h
  have halg : algebraMap R (Q.P ⧸ K) = (Ideal.Quotient.mk K).comp ((algebraMap T.B Q.P).comp (algebraMap R T.B)) :=
    rfl
  let F : Thick κ t :=
    { B := Q.P ⧸ K
      J := (Q.ext T.J).map (Ideal.Quotient.mk K)
      δ := δ'
      nil := (isDPNilpotent_iff_exists_isLevel δ').2 ⟨_, hlev⟩
      dp := by rw [halg]; exact IsDPMorphism.comp _ hδ' (IsDPMorphism.comp _ hη.dp T.dp)
      B₀ := T.B₀
      π := πF
      surj := fun b₀ ↦ by
        obtain ⟨b, rfl⟩ := T.surj b₀
        exact ⟨Ideal.Quotient.mk K (algebraMap T.B Q.P b), by rw [hπF, hε1]⟩
      ker := fun y ↦ by
        obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective y
        rw [Ideal.mem_quotient_iff_mem hKle]
        exact hπ₀ p
      x := T.x
      w := by
        rw [T.w]
        congr 1
        refine RingHom.ext fun r ↦ ?_
        change T.π (algebraMap R T.B r) = T.π (ε (algebraMap T.B Q.P (algebraMap R T.B r)))
        rw [hε1] }
  let φ : T.B →ₐ[R] F.B :=
    { (Ideal.Quotient.mk K).comp (algebraMap T.B Q.P) with commutes' := fun _ ↦ rfl }
  let u : T ⟶ F :=
    ⟨φ, RingHom.id T.B₀, fun b ↦ by
      change T.π b = T.π (ε (algebraMap T.B Q.P b)); rw [hε1],
     IsDPMorphism.comp _ hδ' hη.dp, by rw [spMap_id, Category.id_comp]⟩
  refine ⟨F, u, fun _ ↦ Ideal.Quotient.mk K (Q.e 1), ⟨hlev, fun _ ↦ Ideal.mem_map_of_mem _ (Q.e_one_mem_ext T.J), ?_⟩, ?_⟩
  · intro S hS a c hc
    have hS' : fil S.δ (n + 1) = ⊥ := hS
    obtain ⟨G, hG1, hG2⟩ := hlift S.B (a.φ : T.B →+* S.B) (fun k ↦ S.δ.dpow k (c ())) (S.δ.dpow_zero (hc ()))
      fun m k ↦ S.δ.mul_dpow (hc ())
    have hGa : G.comp (algebraMap T.B Q.P) = (a.φ : T.B →+* S.B) := RingHom.ext hG1
    have hGdp : IsDPMorphism η S.δ G :=
      GlobalTheory.PDA.PDPoly.isDPMorphism_of_isStd T.B T.J T.δ Q η hη S.B S.J S.δ G (c ()) (hc ()) (by rw [hGa]; exact a.dp)
        hG2
    have hGK : ∀ p ∈ K, G p = 0 := fun p hp ↦ by
      have h := hfil.2.2.2.2.2.2 S.B S.J S.δ G hGdp (n + 1)
      rw [hS', ← hK] at h
      exact (Ideal.mem_bot).1 (h (Ideal.mem_map_of_mem G hp))
    let Gb : Q.P ⧸ K →+* S.B := Ideal.Quotient.lift K G hGK
    have hGb : ∀ p, Gb (Ideal.Quotient.mk K p) = G p := fun p ↦ rfl
    let gφ : F.B →ₐ[R] S.B :=
      { Gb with
        commutes' := fun r ↦ by
          change G (algebraMap T.B Q.P (algebraMap R T.B r)) = _
          rw [hG1]; exact a.φ.commutes r }
    have hgdp : IsDPMorphism F.δ S.δ (gφ : F.B →+* S.B) := by
      refine huniv S.B S.J S.δ Gb ?_
      have : Gb.comp (Ideal.Quotient.mk K) = G := RingHom.ext hGb
      rw [this]; exact hGdp
    let g : F ⟶ S :=
      ⟨gφ, a.φ₀, fun b' ↦ by
        obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective b'
        change a.φ₀ (T.π (ε p)) = S.π (G p)
        rw [a.comm, show a.φ (ε p) = G (algebraMap T.B Q.P (ε p)) from (hG1 _).symm]
        have hm : p - algebraMap T.B Q.P (ε p) ∈ Q.ext T.J :=
          Ideal.mem_sup_right ((hε _).2 (by rw [map_sub, hε1, sub_self]))
        have h2 := hGdp.1 (Ideal.mem_map_of_mem G hm)
        rw [← S.ker, map_sub, map_sub, sub_eq_zero] at h2
        exact h2.symm,
       hgdp, a.pt⟩
    refine ⟨g, ⟨Thick.hom_ext fun b ↦ hG1 b, fun _ ↦ ?_⟩, ?_⟩
    · change G (Q.e 1) = c ()
      rw [hG2 1, S.δ.dpow_one (hc ())]
    · rintro g' ⟨h1, h2⟩
      refine Thick.hom_ext fun b' ↦ ?_
      obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective b'
      change ((g'.φ : F.B →+* S.B).comp (Ideal.Quotient.mk K)) p = G p
      have hHdp : IsDPMorphism η S.δ ((g'.φ : F.B →+* S.B).comp (Ideal.Quotient.mk K)) :=
        IsDPMorphism.comp _ g'.dp hδ'
      refine congrArg (fun f : Q.P →+* S.B ↦ f p) (ringHom_eq_of_basis Q (fun b ↦ ?_) fun k ↦ ?_)
      · change (u ≫ g').φ b = G (algebraMap T.B Q.P b)
        rw [h1]; exact (hG1 b).symm
      · rw [hG2 k, ← hη.var k, hHdp.map_dpow (Q.e_one_mem_ext T.J)]
        change S.δ.dpow k (g'.φ (Ideal.Quotient.mk K (Q.e 1))) = _
        rw [show g'.φ (Ideal.Quotient.mk K (Q.e 1)) = c () from h2 ()]
  · have hsemi : SemiHom (RingHom.id R) (Ideal.Quotient.mk K) := fun r p ↦ map_smul (Ideal.Quotient.mkₐ R K) r p
    exact GlobalTheory.T.poincareLemma_truncated_divPowerPoly_oneVariable R T.B T.J T.δ Q η (Q.P ⧸ K) F.J δ' (Ideal.Quotient.mk K) n hη hT hsemi hδ'
      Ideal.Quotient.mk_surjective rfl (fun b ↦ by rw [Ideal.Quotient.eq_zero_iff_mem, hK]) φ
      (SemiHom.of_algHom u.φ) u.dp fun _ ↦ rfl

end GlobalTheory.PDForm

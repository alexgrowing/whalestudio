import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualMapCompDualMap
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCoboundarySndTr
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InvariantFormAbelianVarietyTranslateValue
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogChernCocycleContractionInvariantFieldTrivialiStatement

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.CechKS
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CechKS

section ChernRep

variable {K : Type} [Field K] {A : Over (Sp K)} [GrpObj A]

def chernRepEv1 {I : Type} {U : I → A.left.Opens} (β : C1 (OSmall U))
    {T T' : Thick (dp0 K) (A.hom ≫ 𝟙 (Sp K))} (φ : T ⟶ T') (h : ∃ i, ⊤ ≤ T.x ⁻¹ᵁ U i) : T'.B :=
  β ⟨T, h⟩ ⟨T', h.imp fun _ ↦ φ.le_preimage⟩ ⟨φ⟩

private theorem snd_signed_sum_add {B : Type} [CommRing B] (a b c d a' b' c' d' : DualNumber B) :
    TrivSqZeroExt.snd (a + a' - (b + b') - (c + c' - (d + d'))) =
      TrivSqZeroExt.snd (a - b - (c - d)) + TrivSqZeroExt.snd (a' - b' - (c' - d')) := by
  simp only [TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_sub]
  abel

theorem prism_add' {I : Type} {U : I → A.left.Opens} (z z' : C2 (OSmall U)) {v : epsR K ⟶ A}
    (hv : IsTangent v) {P Q : GPt A} (φ : P.Hom Q) (h : ∃ i, P.In (U i)) :
    prism (z + z') hv φ h = prism z hv φ h + prism z' hv φ h := by
  simp only [prism, ev2, Pi.add_apply]
  exact snd_signed_sum_add _ _ _ _ _ _ _ _

private theorem snd_signed_sum_zero (B : Type) [CommRing B] :
    TrivSqZeroExt.snd ((0 : DualNumber B) - 0 - (0 - 0)) = 0 := by
  simp

theorem prism_zero' {I : Type} {U : I → A.left.Opens} {v : epsR K ⟶ A}
    (hv : IsTangent v) {P Q : GPt A} (φ : P.Hom Q) (h : ∃ i, P.In (U i)) :
    prism (0 : C2 (OSmall U)) hv φ h = 0 := by
  simp only [prism, ev2, Pi.zero_apply]
  exact snd_signed_sum_zero _

private theorem snd_signed_sum_sub {B : Type} [CommRing B] (a b c d a' b' c' d' : DualNumber B) :
    TrivSqZeroExt.snd (a - a' - (b - b') - (c - c' - (d - d'))) =
      TrivSqZeroExt.snd (a - b - (c - d)) - TrivSqZeroExt.snd (a' - b' - (c' - d')) := by
  simp only [TrivSqZeroExt.snd_sub]
  abel

theorem prism_sub' {I : Type} {U : I → A.left.Opens} (z z' : C2 (OSmall U)) {v : epsR K ⟶ A}
    (hv : IsTangent v) {P Q : GPt A} (φ : P.Hom Q) (h : ∃ i, P.In (U i)) :
    prism (z - z') hv φ h = prism z hv φ h - prism z' hv φ h := by
  simp only [prism, ev2, Pi.sub_apply]
  exact snd_signed_sum_sub _ _ _ _ _ _ _ _

theorem prism_sum' {I J : Type} {U : I → A.left.Opens} (t : Finset J) (z : J → C2 (OSmall U))
    {v : epsR K ⟶ A} (hv : IsTangent v) {P Q : GPt A} (φ : P.Hom Q) (h : ∃ i, P.In (U i)) :
    prism (∑ k ∈ t, z k) hv φ h = ∑ k ∈ t, prism (z k) hv φ h := by
  classical
  refine Finset.induction_on t ?_ ?_
  · rw [Finset.sum_empty, Finset.sum_empty]
    exact prism_zero' hv φ h
  · intro a s ha ih
    rw [Finset.sum_insert ha, Finset.sum_insert ha, prism_add', ih]

theorem triv_sec {P Q : GPt A} (φ : P.Hom Q) : φ.triv ≫ Q.sec = P.sec ≫ φ.dual := by
  apply Thick.hom_ext
  intro b
  rw [Thick.comp_φ, Thick.comp_φ]
  show TrivSqZeroExt.inl (φ.ρ b) = dualAlg φ.ρ (TrivSqZeroExt.inl b)
  ext
  · rw [fst_dualAlg]; rfl
  · rw [snd_dualAlg]; simp

theorem triv_tan {P Q : GPt A} (φ : P.Hom Q) {v : epsR K ⟶ A} (hv : IsTangent v) :
    (φ.tr v).triv ≫ Q.tan hv = P.tan hv ≫ φ.dual := by
  apply Thick.hom_ext
  intro b
  rw [Thick.comp_φ, Thick.comp_φ]
  rfl

variable {I : Type} {U : I → A.left.Opens}

def cochainTangentDiffCoeff (β : C1 (OSmall U)) {v : epsR K ⟶ A} (hv : IsTangent v) : PtFn (A.hom ≫ 𝟙 (Sp K)) :=
  open Classical in fun P ↦ if h : ∃ i, P.In (U i) then
    TrivSqZeroExt.snd (R := P.B) (chernRepEv1 β P.sec h - chernRepEv1 β (P.tan hv) (h.imp fun _ e ↦ e.tr hv))
  else 0

theorem prismContractionTwoCochain_coboundary (β : C1 (OSmall U)) {v : epsR K ⟶ A} (hv : IsTangent v) {P Q : GPt A} (φ : P.Hom Q)
    (h : ∃ i, P.In (U i)) :
    prism (d1 _ β) hv φ h = -TrivSqZeroExt.snd (R := Q.B) (chernRepEv1 β (φ.tr v).triv (h.imp fun _ e ↦ e.tr hv)) +
      (cochainTangentDiffCoeff β hv Q - φ.ρ (cochainTangentDiffCoeff β hv P)) := by
  have snd_d1_lemma {R B C : Type} [CommRing R] [CommRing B] [CommRing C] [Algebra R B]
      [Algebra R C] (ρ : B →ₐ[R] C) (a : C) (y x2 x5 x6 y' x4 : DualNumber C) (x3 x7 : DualNumber B) :
      TrivSqZeroExt.snd ((TrivSqZeroExt.inl a - y + x2 - (dualAlg ρ x3 - y + x4)) -
        (x5 - y' + x6 - (dualAlg ρ x7 - y' + x4))) =
        -TrivSqZeroExt.snd x5 + (TrivSqZeroExt.snd (x2 - x6) - ρ (TrivSqZeroExt.snd (x3 - x7))) := by
    simp only [TrivSqZeroExt.snd_sub, TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_inl, snd_dualAlg, map_sub]
    ring
  have hQ : ∃ i, Q.In (U i) := h.imp fun _ e ↦ e.map φ
  have h3 : ∃ i, (P.tr v).In (U i) := h.imp fun _ e ↦ e.tr hv
  have k1 : ev2 (d1 _ β) φ.triv Q.sec h = Q.sec.φ (chernRepEv1 β φ.triv h) -
      chernRepEv1 β (φ.triv ≫ Q.sec) h + chernRepEv1 β Q.sec hQ := rfl
  have k2 : ev2 (d1 _ β) P.sec φ.dual h = φ.dual.φ (chernRepEv1 β P.sec h) -
      chernRepEv1 β (P.sec ≫ φ.dual) h + chernRepEv1 β φ.dual h := rfl
  have k3 : ev2 (d1 _ β) (φ.tr v).triv (Q.tan hv) h3 = (Q.tan hv).φ (chernRepEv1 β (φ.tr v).triv h3) -
      chernRepEv1 β ((φ.tr v).triv ≫ Q.tan hv) h3 + chernRepEv1 β (Q.tan hv) (hQ.imp fun _ e ↦ e.tr hv) := rfl
  have k4 : ev2 (d1 _ β) (P.tan hv) φ.dual h3 = φ.dual.φ (chernRepEv1 β (P.tan hv) h3) -
      chernRepEv1 β (P.tan hv ≫ φ.dual) h3 + chernRepEv1 β φ.dual h := rfl
  have hs : ∀ x : Q.B, Q.sec.φ x = (TrivSqZeroExt.inl x : DualNumber Q.B) := fun _ ↦ rfl
  have ht : ∀ x : DualNumber Q.B, (Q.tan hv).φ x = x := fun _ ↦ rfl
  have hd : ∀ x : DualNumber P.B, φ.dual.φ x = dualAlg φ.ρ x := fun _ ↦ rfl
  rw [prism, k1, k2, k3, k4, triv_sec φ, triv_tan φ hv]
  simp only [hs, ht, hd, cochainTangentDiffCoeff, dif_pos h, dif_pos hQ]
  exact snd_d1_lemma φ.ρ _ _ _ _ _ _ _ _ _

private theorem ev2_pullback_cupZ (c : Z1 (O (dp0 K) (A.hom ≫ 𝟙 (Sp K)))) (ω : Form (A.hom ≫ 𝟙 (Sp K)))
    {T T' T'' : Thick (dp0 K) (A.hom ≫ 𝟙 (Sp K))} (a : T ⟶ T') (b : T' ⟶ T'') (hT : ∃ i, ⊤ ≤ T.x ⁻¹ᵁ U i) :
    ev2 ((CoefMap.restrict (O (dp0 K) (A.hom ≫ 𝟙 (Sp K))) (IsSmall (dp0 K) (A.hom ≫ 𝟙 (Sp K)) U).ι).pullbackTwoCocycle
      (cupZ _ c ω.1)).1 a b hT = b.φ (ev c a) * ev ω.1 b := rfl

private theorem snd_cup_difference_eq {R B C : Type} [CommRing R] [CommRing B] [CommRing C] [Algebra R B]
    [Algebra R C] (ρ : B →ₐ[R] C) (a t : C) (sQ τQ σQ θQ e w b : DualNumber C) (sP τP θP : DualNumber B)
    (e1 : TrivSqZeroExt.inl a + sQ = dualAlg ρ sP + e) (e2 : b + τQ = dualAlg ρ τP + e)
    (e3 : θQ = dualAlg ρ θP + w) (e4 : σQ - θQ = TrivSqZeroExt.inr t) :
    TrivSqZeroExt.snd ((TrivSqZeroExt.inl a * σQ - dualAlg ρ sP * w) - (b * θQ - dualAlg ρ τP * w)) =
      a * t + (-TrivSqZeroExt.snd ((sQ - τQ) * θQ) - ρ (-TrivSqZeroExt.snd ((sP - τP) * θP))) := by
  have key : TrivSqZeroExt.inl a * σQ - dualAlg ρ sP * w - (b * θQ - dualAlg ρ τP * w) =
      TrivSqZeroExt.inl a * (σQ - θQ) - (sQ - τQ) * θQ + dualAlg ρ ((sP - τP) * θP) := by
    rw [map_mul, map_sub]
    linear_combination θQ * e1 - θQ * e2 + (dualAlg ρ sP - dualAlg ρ τP) * e3
  rw [key, e4, TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_sub, TrivSqZeroExt.inl_mul_inr,
    TrivSqZeroExt.snd_inr, smul_eq_mul, snd_dualAlg, map_neg]
  ring

private theorem ev_sec_and_tan_hom_relation (f : Z1 (O (dp0 K) (A.hom ≫ 𝟙 (Sp K)))) {P Q : GPt A} (φ : P.Hom Q) {v : epsR K ⟶ A}
    (hv : IsTangent v) :
    (Q.sec.φ (ev f φ.triv) + ev f Q.sec = φ.dual.φ (ev f P.sec) + ev f φ.dual) ∧
      ((Q.tan hv).φ (ev f (φ.tr v).triv) + ev f (Q.tan hv) = φ.dual.φ (ev f (P.tan hv)) + ev f φ.dual) := by
  constructor
  · rw [← ev_comp, ← ev_comp, triv_sec]
  · rw [← ev_comp, ← ev_comp, triv_tan]

def cupContractionCorrectionTerm (c : Z1 (O (dp0 K) (A.hom ≫ 𝟙 (Sp K)))) (ω : Form (A.hom ≫ 𝟙 (Sp K))) {v : epsR K ⟶ A}
    (hv : IsTangent v) : PtFn (A.hom ≫ 𝟙 (Sp K)) :=
  fun P ↦ -TrivSqZeroExt.snd (R := P.B) ((ev c P.sec - ev c (P.tan hv)) * ev ω.1 (P.tan hv))

theorem prism_cup' (hA : IsAbelianScheme A) (c : Z1 (O (dp0 K) (A.hom ≫ 𝟙 (Sp K))))
    (ω : Form (A.hom ≫ 𝟙 (Sp K))) {v : epsR K ⟶ A} (hv : IsTangent v) {P Q : GPt A} (φ : P.Hom Q)
    (h : ∃ i, P.In (U i)) :
    prism ((CoefMap.restrict (O (dp0 K) (A.hom ≫ 𝟙 (Sp K)))
      (IsSmall (dp0 K) (A.hom ≫ 𝟙 (Sp K)) U).ι).pullbackTwoCocycle (cupZ _ c ω.1)).1 hv φ h =
      ev c φ.triv * algebraMap K Q.B (tanVal v ω) + (cupContractionCorrectionTerm c ω hv Q - φ.ρ (cupContractionCorrectionTerm c ω hv P)) := by
  have h3 : ∃ i, (P.tr v).In (U i) := h.imp fun _ e ↦ e.tr hv
  have hs : ∀ x : Q.B, Q.sec.φ x = (TrivSqZeroExt.inl x : DualNumber Q.B) := fun _ ↦ rfl
  have ht : ∀ x : DualNumber Q.B, (Q.tan hv).φ x = x := fun _ ↦ rfl
  have hd : ∀ x : DualNumber P.B, φ.dual.φ x = dualAlg φ.ρ x := fun _ ↦ rfl
  have h0 : ev ω.1 (φ.tr v).triv = 0 := ω.2 (φ.tr v).triv rfl rfl
  obtain ⟨e1, e2⟩ := ev_sec_and_tan_hom_relation c φ hv
  have e3 := (ev_sec_and_tan_hom_relation ω.1 φ hv).2
  have hQ4 := ev_sec_sub_ev_tan K A hA v hv ω Q
  rw [hs, hd] at e1
  rw [ht, hd] at e2
  rw [ht, hd, h0, zero_add] at e3
  rw [prism]
  simp only [ev2_pullback_cupZ c ω φ.triv Q.sec h, ev2_pullback_cupZ c ω P.sec φ.dual h,
    ev2_pullback_cupZ c ω (φ.tr v).triv (Q.tan hv) h3, ev2_pullback_cupZ c ω (P.tan hv) φ.dual h3, hs, ht, hd]
  exact snd_cup_difference_eq φ.ρ (ev c φ.triv) (algebraMap K Q.B (tanVal v ω)) (ev c Q.sec) (ev c (Q.tan hv))
    (ev ω.1 Q.sec) (ev ω.1 (Q.tan hv)) (ev c φ.dual) (ev ω.1 φ.dual) (ev c (φ.tr v).triv) (ev c P.sec)
    (ev c (P.tan hv)) (ev ω.1 (P.tan hv)) e1 e2 e3 hQ4

theorem ev_sum_smul' {J : Type} (t : Finset J) (r : J → K) (c : J → Z1 (O (dp0 K) (A.hom ≫ 𝟙 (Sp K))))
    {T T' : Thick (dp0 K) (A.hom ≫ 𝟙 (Sp K))} (φ : T ⟶ T') :
    ev (∑ k ∈ t, r k • c k) φ = ∑ k ∈ t, r k • ev (c k) φ := by
  classical
  refine Finset.induction_on t ?_ ?_
  · rfl
  · intro a s ha ih
    rw [Finset.sum_insert ha, Finset.sum_insert ha, ← ih]
    rfl

theorem prism_sumZ' {I J : Type} {U : I → A.left.Opens} (t : Finset J) (z : J → Z2 (OSmall U))
    {v : epsR K ⟶ A} (hv : IsTangent v) {P Q : GPt A} (φ : P.Hom Q) (h : ∃ i, P.In (U i)) :
    prism (∑ k ∈ t, z k).1 hv φ h = ∑ k ∈ t, prism (z k).1 hv φ h := by
  rw [Submodule.coe_sum]
  exact prism_sum' t (fun k ↦ (z k).1) hv φ h

private theorem triv_coc_lemma_7 {K : Type} [Field K] {A : Over (Sp K)} [GrpObj A] {L : LB A.left}
    {I : Type} [Fintype I] (c : I → Z1 (O (dp0 K) (A.hom ≫ 𝟙 (Sp K)))) (ω : I → Form (A.hom ≫ 𝟙 (Sp K)))
    (β : C1 (OSmall L.U)) (ℓ : Z2 ((IsSmall (dp0 K) (A.hom ≫ 𝟙 (Sp K)) L.U).ι ⋙ O (dp0 K) (A.hom ≫ 𝟙 (Sp K))))
    (hℓ : ∀ T T' T'' φ ψ, (ℓ.1 T T' T'' φ ψ : T''.obj.B) ∈ T''.obj.J)
    (hβ : d1 _ β = ((CoefMap.restrict (O (dp0 K) (A.hom ≫ 𝟙 (Sp K))) (IsSmall (dp0 K) (A.hom ≫ 𝟙 (Sp K)) L.U).ι).pullbackTwoCocycle
      (∑ k, cupZ _ (c k) (ω k).1)).1 - ℓ.1)
    (P Q T : GPt A) (φ : P.Hom Q) (ψ : Q.Hom T) (hP : ∃ i, P.In (L.U i)) :
    chernRepEv1 β (φ.comp ψ).triv hP =
      ψ.ρ (chernRepEv1 β φ.triv hP) + chernRepEv1 β ψ.triv (hP.imp fun _ e ↦ e.map φ) := by
  have hQ : ∃ i, Q.In (L.U i) := hP.imp fun _ e ↦ e.map φ
  have hT : ∃ i, T.In (L.U i) := hQ.imp fun _ e ↦ e.map ψ
  have e := congrFun (congrFun (congrFun (congrFun (congrFun hβ ⟨P.triv, hP⟩) ⟨Q.triv, hQ⟩)
    ⟨T.triv, hT⟩) ⟨φ.triv⟩) ⟨ψ.triv⟩
  have hz0 : ((CoefMap.restrict (O (dp0 K) (A.hom ≫ 𝟙 (Sp K))) (IsSmall (dp0 K) (A.hom ≫ 𝟙 (Sp K)) L.U).ι).pullbackTwoCocycle
      (∑ k, cupZ _ (c k) (ω k).1)).1
      ⟨P.triv, hP⟩ ⟨Q.triv, hQ⟩ ⟨T.triv, hT⟩ ⟨φ.triv⟩ ⟨ψ.triv⟩ = 0 := by
    rw [CoefMap.pullCocycleTwo_apply]
    show Subtype.val (∑ k, cupZ (O (dp0 K) (A.hom ≫ 𝟙 (Sp K))) (c k) (ω k).1) P.triv Q.triv T.triv
      φ.triv ψ.triv = 0
    rw [Submodule.coe_sum]
    simp only [Finset.sum_apply]
    refine Finset.sum_eq_zero fun k _ ↦ ?_
    have hw : (ω k).1.1 Q.triv T.triv ψ.triv = 0 := (ω k).2 ψ.triv rfl rfl
    rw [cupZ_apply, hw, mul_zero]
  have hl0 : ℓ.1 ⟨P.triv, hP⟩ ⟨Q.triv, hQ⟩ ⟨T.triv, hT⟩ ⟨φ.triv⟩ ⟨ψ.triv⟩ = 0 :=
    Ideal.mem_bot.mp (hℓ ⟨P.triv, hP⟩ ⟨Q.triv, hQ⟩ ⟨T.triv, hT⟩ ⟨φ.triv⟩ ⟨ψ.triv⟩)
  simp only [Pi.sub_apply, hz0, hl0, sub_zero] at e
  rw [d1_apply] at e
  have e' : ψ.ρ (chernRepEv1 β φ.triv hP) - chernRepEv1 β (φ.triv ≫ ψ.triv) hP +
      chernRepEv1 β ψ.triv hQ = 0 := e
  have hcomp : (φ.comp ψ).triv = φ.triv ≫ ψ.triv := Thick.hom_ext fun _ ↦ rfl
  rw [sub_add_eq_add_sub, sub_eq_zero] at e'
  rw [hcomp]
  exact e'.symm

private theorem chern_cob_lemma_10 {K : Type} [Field K] {A : Over (Sp K)} [GrpObj A] {L : LB A.left}
    {I : Type} [Fintype I] (c : I → Z1 (O (dp0 K) (A.hom ≫ 𝟙 (Sp K)))) (ω : I → Form (A.hom ≫ 𝟙 (Sp K)))
    (ℓ : Z2 ((IsSmall (dp0 K) (A.hom ≫ 𝟙 (Sp K)) L.U).ι ⋙ O (dp0 K) (A.hom ≫ 𝟙 (Sp K))))
    (hz : (CoefMap.restrict (O (dp0 K) (A.hom ≫ 𝟙 (Sp K))) (IsSmall (dp0 K) (A.hom ≫ 𝟙 (Sp K)) L.U).ι).pull2
      (∑ k, cup _ (H1.mk _ (c k)) (Form.cl _ (ω k))) = H2.mk _ ℓ) :
    ∃ β : C1 (OSmall L.U), d1 _ β = ((CoefMap.restrict (O (dp0 K) (A.hom ≫ 𝟙 (Sp K))) (IsSmall (dp0 K) (A.hom ≫ 𝟙 (Sp K)) L.U).ι).pullbackTwoCocycle
      (∑ k, cupZ _ (c k) (ω k).1)).1 - ℓ.1 ∧ ℓ.1 = ((CoefMap.restrict (O (dp0 K) (A.hom ≫ 𝟙 (Sp K))) (IsSmall (dp0 K) (A.hom ≫ 𝟙 (Sp K)) L.U).ι).pullbackTwoCocycle
      (∑ k, cupZ _ (c k) (ω k).1)).1 - d1 _ β := by
  have hsum : (∑ k, cup _ (H1.mk _ (c k)) (Form.cl _ (ω k))) =
      H2.mk (O (dp0 K) (A.hom ≫ 𝟙 (Sp K))) (∑ k, cupZ _ (c k) (ω k).1) := by
    rw [map_sum]
    refine Finset.sum_congr rfl fun k _ ↦ ?_
    rw [← cup_mk]
    rfl
  rw [hsum, CoefMap.pullCohomologyTwo_class, H2.mk_eq_mk] at hz
  obtain ⟨β, hβ⟩ := hz
  exact ⟨β, hβ, by simp only [hβ, sub_sub_cancel]⟩

private theorem prism_eq_of_pullback_cup_sub_d1 {K : Type} [Field K] {A : Over (Sp K)} [GrpObj A] (hA : IsAbelianScheme A)
    {L : LB A.left} {I : Type} [Fintype I] (c : I → Z1 (O (dp0 K) (A.hom ≫ 𝟙 (Sp K))))
    (ω : I → Form (A.hom ≫ 𝟙 (Sp K))) (β : C1 (OSmall L.U)) (ℓ : C2 (OSmall L.U))
    (hℓ1 : ℓ = ((CoefMap.restrict (O (dp0 K) (A.hom ≫ 𝟙 (Sp K))) (IsSmall (dp0 K) (A.hom ≫ 𝟙 (Sp K)) L.U).ι).pullbackTwoCocycle
      (∑ k, cupZ _ (c k) (ω k).1)).1 - d1 _ β) {v : epsR K ⟶ A} (hv : IsTangent v) (N G3 : PtFn (A.hom ≫ 𝟙 (Sp K)))
    {P Q : GPt A} (φ : P.Hom Q) (hex : ∃ i, P.In (L.U i)) (hN : prism ℓ hv φ hex = N Q - φ.ρ (N P))
    (h3 : TrivSqZeroExt.snd (R := Q.B) (chernRepEv1 β (φ.tr v).triv (hex.imp fun _ e ↦ e.tr hv)) =
      G3 Q - φ.ρ (G3 P)) :
    ev (∑ k, tanVal v (ω k) • c k) φ.triv =
      (N Q - ∑ k, cupContractionCorrectionTerm (c k) (ω k) hv Q - G3 Q + cochainTangentDiffCoeff β hv Q) -
        φ.ρ (N P - ∑ k, cupContractionCorrectionTerm (c k) (ω k) hv P - G3 P + cochainTangentDiffCoeff β hv P) := by
  rw [hℓ1, prism_sub', map_sum, prism_sumZ', prismContractionTwoCochain_coboundary β hv φ hex] at hN
  simp only [prism_cup' hA] at hN
  rw [ev_sum_smul']
  simp only [map_sub, map_add, map_sum]
  have hsm : ∀ k, tanVal v (ω k) • ev (c k) φ.triv =
      ev (c k) φ.triv * algebraMap K Q.B (tanVal v (ω k)) := fun k ↦ by
    rw [Algebra.smul_def, mul_comm]
  simp only [hsm]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib] at hN
  linear_combination hN - h3

end ChernRep

theorem isRep_chern_tanVal : ∀ (K : Type) [Field K] (A : Over (Sp K)) [GrpObj A], IsAbelianScheme A → ∀ (L : LB A.left), L.IsLB → ∀ (I : Type) [Fintype I] (c : I → Z1 (O (dp0 K) (A.hom ≫ 𝟙 (Sp K)))) (ω : I → Form (A.hom ≫ 𝟙 (Sp K))), IsChern (dp0 K) (A.hom ≫ 𝟙 (Sp K)) L (∑ k, cup _ (H1.mk _ (c k)) (Form.cl _ (ω k))) → ∀ v : epsR K ⟶ A, IsTangent v → ∀ (J : Type) (V : J → A.left.affineOpens) (τ : J → L.ι), (∀ j, (V j).1 ≤ L.U (τ j)) → IsRep (fun j => (V j).1) (∑ k, tanVal v (ω k) • c k) (fun j j' => dlog L v (τ j) (τ j')) := by
  intro K _ A _ hA L hL I _ c ω hch v hv J V τ hV
  classical
  have hcov : ⨆ i, L.U i = ⊤ := hL.1
  obtain ⟨i0, hi0, u, ℓ, hu, hℓ, hz⟩ := hch
  obtain ⟨N, hN, hNd⟩ := GlobalTheory.T.logChernCocycle_contraction_invariantField_trivialised K A L hL i0 hi0 u ℓ.1 hu hℓ v hv
  obtain ⟨β, hβ, hℓ1⟩ := chern_cob_lemma_10 c ω ℓ hz
  obtain ⟨G3, hG3⟩ := GlobalTheory.CocInv.exists_coboundary_snd_tr K A hA L.ι L.U hcov
    (fun P Q φ ↦ if hP : ∃ i, P.In (L.U i) then chernRepEv1 β φ.triv hP else 0)
    (by
      intro P Q T φ ψ hP
      have hQ : ∃ i, Q.In (L.U i) := hP.imp fun _ e ↦ e.map φ
      simp only [dif_pos hP, dif_pos hQ]
      exact triv_coc_lemma_7 c ω β ℓ (fun T T' T'' φ ψ ↦ (hℓ T T' T'' φ ψ).1) hβ P Q T φ ψ hP) v hv
  refine ⟨fun j P ↦ N (τ j) P - ∑ k, cupContractionCorrectionTerm (c k) (ω k) hv P - G3 P + cochainTangentDiffCoeff β hv P, ?_, ?_⟩
  · intro j P Q φ hP
    have hP' : P.In (L.U (τ j)) := hP.mono (hV j)
    have h3 := hG3 (τ j) (V j) (hV j) P Q φ hP
    simp only [dif_pos (show ∃ i, (P.tr v).In (L.U i) from ⟨τ j, hP'.tr hv⟩)] at h3
    exact prism_eq_of_pullback_cup_sub_d1 hA c ω β ℓ.1 hℓ1 hv (N (τ j)) G3 φ ⟨τ j, hP'⟩ (hN (τ j) P Q φ hP') h3
  · intro j j' P hj hj'
    have := hNd (τ j) (τ j') P (hj.mono (hV j)) (hj'.mono (hV j'))
    show N (τ j) P - _ - G3 P + _ - (N (τ j') P - _ - G3 P + _) = dlog L v (τ j) (τ j') P
    rw [← this]
    abel

end GlobalTheory.CechKS

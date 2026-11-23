import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.FinModel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagPotentialBlockDecomposition
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EighthPowerProjectionsGroupPullback
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorInverseHeckeTranslatesForgetLevel

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.UPel.HT.EtLev GlobalTheory.LKTrip GlobalTheory.LKGeo
open scoped TensorProduct
open GlobalTheory.CechPic
open UpperTheory.Gal.Int.Geo

section Over

variable {X : Scheme.{0}} {U V A B : Over X} [GrpObj U] [GrpObj V] [GrpObj A] [GrpObj B]

private theorem cartIso {φ : A.left ⟶ B.left} (h : IsGrpPullback A B (𝟙 X) φ) :
    ∃ e : A ≅ B, e.hom.left = φ ∧ IsMonHom e.hom := by
  haveI : IsIso φ := h.1.isIso_fst_of_isIso
  have hw : φ ≫ B.hom = A.hom := by simpa using h.1.w
  have he : (Over.isoMk (asIso φ) hw).hom.left = φ := rfl
  refine ⟨Over.isoMk (asIso φ) hw, rfl, ?_⟩
  apply GlobalTheory.GrpPullPow.isMonHom_of_mul_pts
  intro T x y
  apply Over.OverMorphism.ext
  let j : Over.mk (T.hom ≫ 𝟙 X) ⟶ T := Over.homMk (𝟙 T.left) (by simp)
  have key := h.2 T x y (j ≫ x ≫ (Over.isoMk (asIso φ) hw).hom) (j ≫ y ≫ (Over.isoMk (asIso φ) hw).hom)
    (by simp [j, he]) (by simp [j, he])
  rw [← MonObj.comp_mul] at key
  simpa [j, he] using key.symm

private theorem quasiInv (e₁ : U ≅ A) (e₂ : V ≅ B) [IsMonHom e₁.hom] (ψ : U ⟶ V) (ψ' : V ⟶ U) (n : ℕ)
    (h : ψ ≫ ψ' = 𝟙 U ^ n) : (e₁.inv ≫ ψ ≫ e₂.hom) ≫ e₂.inv ≫ ψ' ≫ e₁.hom = 𝟙 A ^ n := by
  have h2 : (e₁.inv ≫ ψ ≫ e₂.hom) ≫ e₂.inv ≫ ψ' ≫ e₁.hom = e₁.inv ≫ (ψ ≫ ψ') ≫ e₁.hom := by simp
  rw [h2, h, MonObj.pow_comp, MonObj.comp_pow, Category.id_comp, Iso.inv_hom_id]

private theorem kerIff (e₁ : U ≅ A) (e₂ : V ≅ B) [IsMonHom e₂.hom] (ψ : U ⟶ V) {T : Over X} (g : T ⟶ U) :
    (g ≫ e₁.hom) ≫ e₁.inv ≫ ψ ≫ e₂.hom = 1 ↔ g ≫ ψ = 1 := by
  have e : (g ≫ e₁.hom) ≫ e₁.inv ≫ ψ ≫ e₂.hom = (g ≫ ψ) ≫ e₂.hom := by simp
  rw [e]
  refine ⟨fun h => ?_, fun h => by rw [h, one_comp]⟩
  have := congrArg (· ≫ e₂.inv) h
  simpa [one_comp] using this

end Over

private theorem isoEqOne {X : Scheme.{0}} {A B : Over X} [GrpObj A] [GrpObj B] (e : A ≅ B) [IsMonHom e.hom] {T : Over X} (y : T ⟶ A) :
    y ≫ e.hom = 1 ↔ y = 1 := by
  constructor
  · intro h
    have h' : y = (y ≫ e.hom) ≫ e.inv := by simp
    rw [h', h, MonObj.one_comp]
  · rintro rfl
    exact MonObj.one_comp _

section Pol

variable {X : Scheme.{0}} {U V A B : Over X} [GrpObj U] [IsCommMonObj U] [GrpObj V] [IsCommMonObj V]
  [GrpObj A] [IsCommMonObj A] [GrpObj B] [IsCommMonObj B]

private theorem square_id : Hecke.sq2 (𝟙 B) = 𝟙 (G2 B).left := by
  unfold Hecke.sq2
  simp

private theorem isIso_sq (e : A ≅ B) {φ₂ : (G2 A).left ⟶ (G2 B).left} (h : Geo.Tor.IsSquare e.hom.left φ₂) :
    IsIso φ₂ := by
  have hsq : Geo.Tor.IsSquare (𝟙 A.left) (𝟙 (G2 A).left) := by
    constructor <;> simp
  have key := ES.PIsogExt.isSquare_square_compatible_homs hsq h (ψ₀ := 𝟙 A) (ψ := e.hom) (by simp)
  rw [square_id, Category.id_comp, Category.id_comp] at key
  rw [← key]
  refine ⟨⟨Hecke.sq2 e.inv, ?_, ?_⟩⟩
  · rw [← Hecke.Comp.grpSchemeSquareProductMap_comp, e.hom_inv_id, square_id]
  · rw [← Hecke.Comp.grpSchemeSquareProductMap_comp, e.inv_hom_id, square_id]

private theorem polMove {PU : LB (G2 U).left} {PV : LB (G2 V).left} {PA : LB (G2 A).left} {PB : LB (G2 B).left}
    (hU : PU.IsLB) (hV : PV.IsLB) (hA : PA.IsLB) (hB : PB.IsLB) (e₁ : U ≅ A) (e₂ : V ≅ B) (ψ : U ⟶ V) (χ : A ⟶ B)
    (he : e₁.hom.left ≫ χ.left = ψ.left ≫ e₂.hom.left) {φ₁ : (G2 U).left ⟶ (G2 A).left} {φ₂ : (G2 V).left ⟶ (G2 B).left}
    (s₁ : Geo.Tor.IsSquare e₁.hom.left φ₁) (s₂ : Geo.Tor.IsSquare e₂.hom.left φ₂)
    (l₁ : LBIso PU (PA.pull φ₁)) (l₂ : LBIso PV (PB.pull φ₂)) (c : ℕ)
    (l : LBIso (Hecke.lbPow PU c) (PV.pull (Hecke.sq2 ψ))) :
    LBIso (Hecke.lbPow PA c) (PB.pull (Hecke.sq2 χ)) := by
  haveI : IsIso φ₁ := isIso_sq e₁ s₁
  have key : φ₁ ≫ Hecke.sq2 χ = Hecke.sq2 ψ ≫ φ₂ := ES.PIsogExt.isSquare_square_compatible_homs s₁ s₂ he
  have hPAc : (Hecke.lbPow PA c).IsLB := LB.isLB_linComb hA _ _
  have hPUc : (Hecke.lbPow PU c).IsLB := LB.isLB_linComb hU _ _
  have hPBχ : (PB.pull (Hecke.sq2 χ)).IsLB := pull_isLB hB _
  rw [← cls_eq_iff hPAc hPBχ]
  have inj : ∀ x y : Pic (G2 A).left, pull φ₁ x = pull φ₁ y → x = y := by
    intro x y hxy
    have hh := congrArg (pull (inv φ₁)) hxy
    rwa [← pull_comp, ← pull_comp, IsIso.inv_hom_id, pull_id, pull_id] at hh
  have h1 : cls PU hU = pull φ₁ (cls PA hA) := by
    rw [← cls_pull hA φ₁ (pull_isLB hA φ₁)]
    exact (cls_eq_iff _ _).2 l₁
  have h2 : cls PV hV = pull φ₂ (cls PB hB) := by
    rw [← cls_pull hB φ₂ (pull_isLB hB φ₂)]
    exact (cls_eq_iff _ _).2 l₂
  have h3 : cls (Hecke.lbPow PU c) hPUc = cls (PV.pull (Hecke.sq2 ψ)) (pull_isLB hV _) := (cls_eq_iff _ _).2 l
  rw [Hecke.Comp.cls_lbPow' hU c hPUc, cls_pull hV] at h3
  apply inj
  rw [Hecke.Comp.cls_lbPow' hA c hPAc, cls_pull hB _ hPBχ, map_nsmul, ← h1, h3, h2, ← pull_comp,
    ← pull_comp, key]

end Pol

private theorem intMul {p : ℕ} [Fact p.Prime] {a b : AfP p} (ha : IsIntAf a) (hb : IsIntAf b) : IsIntAf (a * b) := fun v => by
  rw [map_mul]; exact mul_mem (ha v) (hb v)

private theorem inAf_mem {p : ℕ} [Fact p.Prime] (D : Datum p) (x : D.La) : inAf D x ∈ LaHat D :=
  AddSubgroup.subset_closure ⟨1, x, fun v => by rw [map_one]; exact one_mem _, rfl⟩

private theorem numEq {p : ℕ} [Fact p.Prime] {c₀ M : ℕ} (hc : c₀.Coprime p) (hM : M.Coprime p) {t t' t₁ t₁' m₀ t₂ : AfP p}
    (ht : IsIntAf t) (ht' : IsIntAf t') (htt : t * t' = 1) (i1 : IsIntAf t₁) (i1' : IsIntAf t₁') (e1 : t₁ * t₁' = 1)
    (im₀ : IsIntAf m₀) (i2 : IsIntAf t₂) (e2 : m₀ * t₂ = 1) (e : (M : AfP p) * t₁ * m₀ = c₀ * t)
    (H : ∀ (c c' : ℕ) (t t' : AfP p), c.Coprime p → c'.Coprime p → IsIntAf t → IsIntAf t' → t * t' = 1 → (c : AfP p) = c' * t → c = c') :
    c₀ = M := by
  refine H c₀ M (t₁ * m₀ * t') (t₁' * t₂ * t) hc hM (intMul (intMul i1 im₀) ht') (intMul (intMul i1' i2) ht) ?_ ?_
  · calc t₁ * m₀ * t' * (t₁' * t₂ * t) = (t₁ * t₁') * (m₀ * t₂) * (t * t') := by ring
      _ = 1 := by rw [e1, e2, htt]; ring
  · calc (c₀ : AfP p) = c₀ * t * t' := by rw [_root_.mul_assoc, htt, _root_.mul_one]
      _ = M * (t₁ * m₀ * t') := by rw [← e]; ring

theorem UpperTheory.heckeCorrespondence_isogeny_of_trace_crt :
    TrEta → TrBack → TrTj → MultUnit → CongCRT → TjIsog := by
  intro hTE hTB hTT hMU hCRT
  intro p _ D G L E _ _ gb w q _ r 𝔴 𝔫 S k T K₀ hLev i h hTj hIh u hu N' N c' c hN' hN W s₀ o₁ o₂ n₁ n₂
  obtain ⟨hu1, huC⟩ := (hLev u).1 hu
  have hIu : Integ L u := integ_of_mem hu1
  rw [S.lev] at huC
  have huN₀ : L.CongOne S.N₀ u := ((hCRT p D G L q r S.N₀ S.𝔞 S.std.cop S.upow u hIu).1.1 huC).1
  have hhN₀ : L.CongOne S.N₀ h := hTj.away S.N₀ S.std.cop
  have hhu : L.CongOne S.N₀ (h * u) := Link.CongOne.mul L hhN₀ huN₀
  obtain ⟨e₁, he₁, hm₁⟩ := cartIso n₁.cart
  obtain ⟨e₂, he₂, hm₂⟩ := cartIso n₂.cart
  haveI := hm₁
  haveI := hm₂
  haveI : IsMonHom W.ψ := W.trans.1
  have hM : Ideal.absNorm 𝔴 ^ i = q ^ (S.f * i) := by
    rw [S.std.norm, pow_mul]
  have hqp : q.Coprime p := (Nat.coprime_primes (Fact.out) (Fact.out)).2 S.atq.ne
  have hMcop : (q ^ (S.f * i)).Coprime p := Nat.Coprime.pow_left _ hqp
  have hsq : n₁.φ ≫ Over.Hom.left (e₁.inv ≫ W.ψ ≫ e₂.hom) = Over.Hom.left W.ψ ≫ n₂.φ := by
    rw [← he₁, ← he₂]
    simp only [Over.comp_left]
    rw [← Category.assoc, ← Over.comp_left, e₁.hom_inv_id]
    simp
  have a1 : ∀ d : D.O, (T.M N').univ.act.act d ≫ e₁.hom = e₁.hom ≫ o₁.act.act d := by
    intro d
    apply Over.OverMorphism.ext
    simp only [Over.comp_left, he₁]
    exact n₁.act d
  have a1' : ∀ d : D.O, o₁.act.act d ≫ e₁.inv = e₁.inv ≫ (T.M N').univ.act.act d := by
    intro d
    rw [Iso.comp_inv_eq, Category.assoc, a1, Iso.inv_hom_id_assoc]
  have a2 : ∀ d : D.O, W.o.act.act d ≫ e₂.hom = e₂.hom ≫ o₂.act.act d := by
    intro d
    apply Over.OverMorphism.ext
    simp only [Over.comp_left, he₂]
    exact n₂.act d
  refine ⟨e₁.inv ≫ W.ψ ≫ e₂.hom, hsq, ?_, ?_⟩
  · refine ⟨⟨S.f * i, rfl⟩, inferInstance, ?_, ?_, ?_, ?_⟩
    · intro d
      rw [reassoc_of% (a1' d), reassoc_of% (W.trans.2.1 d), a2]
      simp only [Category.assoc]
    · intro x
      have b1' : (T.M N').univ.eta (c' • x) ≫ e₁.hom = o₁.eta x := by
        apply Over.OverMorphism.ext
        simp only [Over.comp_left, he₁]
        simpa using n₁.eta x
      have b1 : o₁.eta x ≫ e₁.inv = (T.M N').univ.eta (c' • x) := by
        rw [Iso.comp_inv_eq]
        exact b1'.symm
      have b2 : W.o.eta (c • x) ≫ e₂.hom = o₂.eta x := by
        apply Over.OverMorphism.ext
        simp only [Over.comp_left, he₂]
        simpa using n₂.eta x
      have b3 : (T.M N').univ.eta (c' • x) ≫ W.ψ = W.o.eta (c • x) :=
        hTE p D G L E gb (h * u) (T.M N').X (T.M N').s N' N (T.M N').univ W.o W.ψ W.trans S.N₀ c' c hN' hN
          x x (hhu _ (inAf_mem D x))
      rw [reassoc_of% b1, reassoc_of% b3, b2]
    · obtain ⟨c₀, hc₀, ⟨hl⟩, t, t', ht, ht', htt, hmul⟩ := W.trans.2.2.2.1
      obtain ⟨t₁, t₁', i1, i1', e1, hh⟩ := hTj.mult
      obtain ⟨t₂, im₀, i2, e2⟩ := (hMU p D G L).1 u hu1
      have hc : c₀ = q ^ (S.f * i) := by
        refine numEq hc₀ hMcop ht ht' htt i1 i1' e1 im₀ i2 e2 ?_ (hMU p D G L).2
        rw [← hmul, ← hM]
        push_cast at hh ⊢
        rw [← hh]
        simp [Units.val_mul]
      rw [← hc]
      refine ⟨polMove (T.M N').univ.isLB W.o.isLB o₁.isLB o₂.isLB e₁ e₂ W.ψ (e₁.inv ≫ W.ψ ≫ e₂.hom) ?_
        (by rw [he₁]; exact n₁.sq) (by rw [he₂]; exact n₂.sq) n₁.pol n₂.pol c₀ hl⟩
      rw [he₁, he₂]
      exact hsq
    · have hback : ∀ v ∈ LaHat D, ∃ v' ∈ LaHat D, (L.actG (h * u)) v' = (q ^ (S.f * i)) • v := by
        intro v hv
        obtain ⟨v'', hv'', hvv⟩ := hTj.back v hv
        have hui : L.CongOne 1 u⁻¹ := hu1.2
        obtain ⟨w₁, hw₁, hw⟩ := hui v'' hv''
        refine ⟨L.actG u⁻¹ v'', ?_, ?_⟩
        · rw [hw, one_smul]
          exact add_mem hv'' hw₁
        · rw [map_mul, Module.End.mul_apply, ← Module.End.mul_apply (L.actG u), ← map_mul, mul_inv_cancel,
            map_one, Module.End.one_apply, hvv, hM]
      obtain ⟨ψ', hψ', h1, h2⟩ := hTB p D G L E gb (h * u) (T.M N').X (T.M N').s N' N (T.M N').univ W.o W.ψ
        W.trans _ hMcop hback
      haveI := hψ'
      exact ⟨e₂.inv ≫ ψ' ≫ e₁.hom, inferInstance, quasiInv e₁ e₂ W.ψ ψ' _ h1, quasiInv e₂ e₁ ψ' W.ψ _ h2⟩
  · intro kk _ _ _ x
    obtain ⟨hT1, hT2⟩ := hTT p D G L E gb (h * u) (T.M N').X (T.M N').s N' N (T.M N').univ W.o W.ψ W.trans q r 𝔴
      i h u S.atq hTj hIh hu1 rfl kk x
    have hk : ∀ (g : Over.mk x ⟶ o₁.A) (d : D.O), g ≫ o₁.act.act d = 1 ↔ (g ≫ e₁.inv) ≫ (T.M N').univ.act.act d = 1 := by
      intro g d
      rw [Category.assoc, ← a1' d, ← Category.assoc]
      haveI : IsMonHom e₁.symm.hom := (inferInstance : IsMonHom e₁.inv)
      exact (isoEqOne e₁.symm (g ≫ o₁.act.act d)).symm
    have hker : ∀ g : Over.mk x ⟶ o₁.A, g ≫ (e₁.inv ≫ W.ψ ≫ e₂.hom) = 1 ↔ (g ≫ e₁.inv) ≫ W.ψ = 1 := by
      intro g
      have := kerIff e₁ e₂ W.ψ (g ≫ e₁.inv)
      simpa using this
    refine ⟨?_, ?_⟩
    · intro g hg ⟨e, he⟩ a ha
      rw [hk]
      refine hT1 (g ≫ e₁.inv) ((hker g).1 hg) ⟨e, fun y hy => (hk g _).1 (he y hy)⟩ a ha
    · rw [S.std.m1, _root_.one_mul, ← hT2]
      refine Nat.card_congr (Equiv.subtypeEquiv
        ⟨fun g => g ≫ e₁.inv, fun g => g ≫ e₁.hom, fun g => by simp, fun g => by simp⟩ ?_)
      intro g
      refine and_congr (hker g) ?_
      exact forall₂_congr fun a _ => hk g _

import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.FiniteEtaleModels.SecInjG
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.IdealSplit
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagPotentialBlockDecomposition
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ZarhinOrderIsRingActionOnProduct

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.UPel.HT.EtLev GlobalTheory.LKTrip GlobalTheory.LKGeo
open UpperTheory.Gal.Int.Geo
open UpperTheory.Gal.crystallineComparison.Mod (Std TjD KerAt)
open scoped TensorProduct
open UpperTheory.Gal.FiniteEtaleModels

namespace UpperTheory.Gal.FiniteEtaleModels

section Grp

variable {X : Scheme.{0}}

private theorem exists_iso_of_cart {A B : Over X} [GrpObj A] [GrpObj B] {φ : A.left ⟶ B.left}
    (h : IsGrpPullback A B (𝟙 X) φ) : ∃ e : A ≅ B, e.hom.left = φ ∧ IsMonHom e.hom ∧ IsMonHom e.inv := by
  have hφ : IsIso φ := h.1.isIso_fst_of_isIso
  have hw : (asIso φ).hom ≫ B.hom = A.hom := by simpa using h.1.w
  have hel : (Over.isoMk (asIso φ) hw).hom.left = φ := rfl
  have he : IsMonHom (Over.isoMk (asIso φ) hw).hom := by
    refine GlobalTheory.ZarhinFam.RAct.isMonHom_of_mul_comp _ ?_
    intro T x y
    let i : Over.mk (T.hom ≫ 𝟙 X) ⟶ T := Over.homMk (𝟙 T.left) (by simp)
    have key := h.2 T x y (i ≫ x ≫ (Over.isoMk (asIso φ) hw).hom)
      (i ≫ y ≫ (Over.isoMk (asIso φ) hw).hom) (by simp [i, hel]) (by simp [i, hel])
    rw [← MonObj.comp_mul] at key
    apply Over.OverMorphism.ext
    have hi : i.left = 𝟙 T.left := rfl
    rw [Over.comp_left, hi] at key
    rw [Over.comp_left, hel]
    exact key.symm.trans (Category.id_comp _)
  exact ⟨Over.isoMk (asIso φ) hw, rfl, he, inferInstance⟩

private theorem comp_pow_id {A B : Over X} [GrpObj A] [GrpObj B] (e : A ⟶ B) [IsMonHom e] (n : ℕ) :
    ((𝟙 A) ^ n) ≫ e = e ≫ ((𝟙 B) ^ n) := by
  rw [MonObj.pow_comp, MonObj.comp_pow, Category.id_comp, Category.comp_id]

private theorem comp_iso_eq_one {A B T : Over X} [GrpObj A] [GrpObj B] (e : A ≅ B) [IsMonHom e.hom] [IsMonHom e.inv] (a : T ⟶ A) :
    a ≫ e.hom = 1 ↔ a = 1 := by
  constructor
  · intro h
    calc a = (a ≫ e.hom) ≫ e.inv := by simp
      _ = 1 := by rw [h, MonObj.one_comp]
  · rintro rfl
    exact MonObj.one_comp _

end Grp

private theorem lbIso_move {Y Y₁ Z Z₁ : Scheme.{0}} {P : LB Y} {P₁ : LB Y₁} {Q : LB Z} {Q₁ : LB Z₁}
    (hP : P.IsLB) (hP₁ : P₁.IsLB) (hQ : Q.IsLB) (hQ₁ : Q₁.IsLB) (f : Y ⟶ Y₁) [IsIso f] (g : Z ⟶ Z₁) (a : Y ⟶ Z) (a₁ : Y₁ ⟶ Z₁)
    (w : f ≫ a₁ = a ≫ g) (c : ℕ) (h₁ : LBIso P (P₁.pull f)) (h₂ : LBIso Q (Q₁.pull g))
    (h : LBIso (Hecke.lbPow P c) (Q.pull a)) : LBIso (Hecke.lbPow P₁ c) (Q₁.pull a₁) := by
  have hPc : ∀ {Z : Scheme.{0}} (L : LB Z), L.IsLB → (Hecke.lbPow L c).IsLB := by
    intro Z L hL
    unfold Hecke.lbPow
    exact LB.isLB_linComb hL _ _
  have pw : ∀ {Z : Scheme.{0}} (L : LB Z) (hL : L.IsLB) (h' : (Hecke.lbPow L c).IsLB),
      GlobalTheory.CechPic.cls _ h' = c • GlobalTheory.CechPic.cls L hL := by
    intro Z L hL h'
    unfold Hecke.lbPow at h' ⊢
    rw [GlobalTheory.CechPic.cls_linComb hL]
    simp [GlobalTheory.CechPic.pull_id]
  rw [← GlobalTheory.CechPic.cls_eq_iff (hPc P₁ hP₁) (pull_isLB hQ₁ a₁)]
  rw [← GlobalTheory.CechPic.cls_eq_iff hP (pull_isLB hP₁ f)] at h₁
  rw [← GlobalTheory.CechPic.cls_eq_iff hQ (pull_isLB hQ₁ g)] at h₂
  rw [← GlobalTheory.CechPic.cls_eq_iff (hPc P hP) (pull_isLB hQ a)] at h
  rw [GlobalTheory.CechPic.cls_pull hP₁] at h₁
  rw [GlobalTheory.CechPic.cls_pull hQ₁] at h₂
  rw [GlobalTheory.CechPic.cls_pull hQ, pw P hP, h₁, h₂, ← map_nsmul, ← GlobalTheory.CechPic.pull_comp, ← w,
    GlobalTheory.CechPic.pull_comp] at h
  rw [pw P₁ hP₁, GlobalTheory.CechPic.cls_pull hQ₁]
  have inj : ∀ z, GlobalTheory.CechPic.pull (inv f) (GlobalTheory.CechPic.pull f z) = z := by
    intro z
    rw [← GlobalTheory.CechPic.pull_comp, IsIso.inv_hom_id, GlobalTheory.CechPic.pull_id]
  rw [← inj (c • _), h, inj]

private theorem isIntAf_mul {p : ℕ} [Fact p.Prime] {a b : AfP p} (ha : IsIntAf a) (hb : IsIntAf b) : IsIntAf (a * b) := fun v => by
  rw [map_mul]
  exact mul_mem (ha v) (hb v)

private theorem inAf_mem {p : ℕ} [Fact p.Prime] (D : Datum p) (x : D.La) : inAf D x ∈ LaHat D :=
  AddSubgroup.subset_closure ⟨1, x, fun v => by rw [map_one]; exact one_mem _, rfl⟩

end UpperTheory.Gal.FiniteEtaleModels

theorem UpperTheory.Gal.FiniteEtaleModels.isogG_of :
    TrEta → TrBack → MultUnit → TrTj → IsogG := by
  intro hTE hTB hMU hTT p hp D G L R' _ _ gb q hq r 𝔴₀ 𝔴 atq sp hm h𝔴 hle R _ b N₀ hN₀ i e hnorm h u hTj hInt hu N' N c' c hN' hN X s o' o ψ hψ s₀ o₁ o₂ n₁ n₂
  obtain ⟨e₁, he₁, m₁, m₁'⟩ := exists_iso_of_cart n₁.cart
  obtain ⟨e₂, he₂, m₂, m₂'⟩ := exists_iso_of_cart n₂.cart
  have mψ : IsMonHom ψ := hψ.1
  have hu1 : u ∈ L.KN 1 := KN_anti (one_dvd N₀) hu
  have atP : AtPrime D q r 𝔴 := ⟨atq.prime, atq.ne, atq.disc, atq.root, atq.perf, h𝔴, hle⟩
  have hcop : (q ^ e).Coprime p :=
    Nat.Coprime.pow_left e ((Nat.coprime_primes atq.prime hp.out).2 atq.ne)
  have hact₁ : ∀ x, o'.act.act x ≫ e₁.hom = e₁.hom ≫ o₁.act.act x := by
    intro x
    apply Over.OverMorphism.ext
    simpa [Over.comp_left, he₁] using n₁.act x
  have hact₂ : ∀ x, o.act.act x ≫ e₂.hom = e₂.hom ≫ o₂.act.act x := by
    intro x
    apply Over.OverMorphism.ext
    simpa [Over.comp_left, he₂] using n₂.act x
  have heta₁ : ∀ y, o'.eta (c' • y) ≫ e₁.hom = o₁.eta y := by
    intro y
    apply Over.OverMorphism.ext
    rw [Over.comp_left, he₁]
    exact (n₁.eta y).trans (Category.id_comp _)
  have heta₂ : ∀ y, o.eta (c • y) ≫ e₂.hom = o₂.eta y := by
    intro y
    apply Over.OverMorphism.ext
    rw [Over.comp_left, he₂]
    exact (n₂.eta y).trans (Category.id_comp _)
  have hsq : n₁.φ ≫ (e₁.inv ≫ ψ ≫ e₂.hom).left = ψ.left ≫ n₂.φ := by
    have hh : e₁.hom.left ≫ e₁.inv.left = 𝟙 _ := by
      rw [← Over.comp_left, e₁.hom_inv_id, Over.id_left]
    rw [← he₁, ← he₂, Over.comp_left, Over.comp_left, ← Category.assoc, hh, Category.id_comp]
  refine ⟨e₁.inv ≫ ψ ≫ e₂.hom, hsq, ⟨⟨e, rfl⟩, inferInstance, ?_, ?_, ?_, ?_⟩, ?_⟩
  · intro x
    have h1 : o₁.act.act x = e₁.inv ≫ o'.act.act x ≫ e₁.hom := by
      rw [Iso.eq_inv_comp]
      exact (hact₁ x).symm
    rw [h1]
    simp only [Category.assoc, Iso.hom_inv_id_assoc]
    rw [reassoc_of% (hψ.2.1 x)]
    exact congrArg (fun t => e₁.inv ≫ ψ ≫ t) (hact₂ x)
  · intro x
    have hE : o'.eta (c' • x) ≫ ψ = o.eta (c • x) := by
      refine hTE p D G L R' gb (h * u) X s N' N o' o ψ hψ N₀ c' c hN' hN x x ?_
      exact Link.CongOne.mul L (hTj.away N₀ hN₀) hu.1 (inAf D x) (inAf_mem D x)
    have a1 : o₁.eta x = o'.eta (c' • x) ≫ e₁.hom := (heta₁ x).symm
    have a2 : o₂.eta x = o.eta (c • x) ≫ e₂.hom := (heta₂ x).symm
    rw [a1, a2]
    simp only [Category.assoc, Iso.hom_inv_id_assoc]
    exact ((reassoc_of% hE) e₂.hom).symm
  · obtain ⟨c₀, hc₀, ⟨hL⟩, t, t', ht, ht', htt, hht⟩ := hψ.2.2.2.1
    obtain ⟨t₁, t₁', ht₁, ht₁', htt₁, hh₁⟩ := hTj.mult
    obtain ⟨t₂', hu₂, ht₂', htt₂⟩ := (hMU p D G L).1 u hu1
    simp only [Subgroup.coe_mul, Prod.snd_mul, Units.val_mul] at hht
    have hc : c₀ = q ^ e := by
      refine (hMU p D G L).2 c₀ (q ^ e) (t₁ * _ * t') (t * t₂' * t₁') hc₀ hcop
        (isIntAf_mul (isIntAf_mul ht₁ hu₂) ht') (isIntAf_mul (isIntAf_mul ht ht₂') ht₁') ?_ ?_
      · rw [show ∀ a b c d f g : AfP p, a * b * c * (d * f * g) = (a * g) * (b * f) * (d * c) from
          fun _ _ _ _ _ _ => by ring, htt₁, htt₂, htt, _root_.one_mul, _root_.one_mul]
      · rw [← _root_.mul_one (c₀ : AfP p), ← htt, ← _root_.mul_assoc, ← hht, hh₁, hnorm]
        ring
    subst hc
    have hiso₁ : IsIso n₁.φ₂ :=
      (GlobalTheory.SiegDesc.isPullback_of_isSquare n₁.cart.1 n₁.sq).isIso_fst_of_isIso
    have hw := ES.PIsogExt.isSquare_square_compatible_homs n₁.sq n₂.sq hsq
    exact ⟨lbIso_move o'.isLB o₁.isLB o.isLB o₂.isLB n₁.φ₂ n₂.φ₂ _ _ hw (q ^ e) n₁.pol n₂.pol hL⟩
  · have hback : ∀ v ∈ LaHat D, ∃ v' ∈ LaHat D, L.actG (h * u) v' = (q ^ e) • v := by
      intro v hv
      obtain ⟨v', hv', hv'e⟩ := hTj.back v hv
      obtain ⟨w, hw, hw'⟩ := hu.2 v' hv'
      have hinv : L.actG u (L.actG u⁻¹ v') = v' := by
        rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
      refine ⟨L.actG u⁻¹ v', ?_, ?_⟩
      · rw [hw']
        exact add_mem hv' (nsmul_mem hw _)
      · rw [map_mul, Module.End.mul_apply, hinv, hv'e, hnorm]
    obtain ⟨ψ', mψ', h1, h2⟩ := hTB p D G L R' gb (h * u) X s N' N o' o ψ hψ (q ^ e) hcop hback
    refine ⟨e₂.inv ≫ ψ' ≫ e₁.hom, inferInstance, ?_, ?_⟩
    · simp only [Category.assoc, Iso.hom_inv_id_assoc]
      rw [reassoc_of% h1, comp_pow_id, Iso.inv_hom_id_assoc]
    · simp only [Category.assoc, Iso.hom_inv_id_assoc]
      rw [reassoc_of% h2, comp_pow_id, Iso.inv_hom_id_assoc]
  · intro k _ _ _ x
    obtain ⟨hT1, hT2⟩ := hTT p D G L R' gb (h * u) X s N' N o' o ψ hψ q r 𝔴 i h u atP hTj hInt hu1 rfl k x
    have hk : ∀ {T : Over X} (g : T ⟶ o₁.A) (a : D.O),
        g ≫ o₁.act.act a = 1 ↔ (g ≫ e₁.inv) ≫ o'.act.act a = 1 := by
      intro T g a
      rw [← comp_iso_eq_one e₁ ((g ≫ e₁.inv) ≫ o'.act.act a)]
      simp only [Category.assoc]
      rw [show o'.act.act a ≫ e₁.hom = e₁.hom ≫ o₁.act.act a from hact₁ a, Iso.inv_hom_id_assoc]
    have hz : ∀ {T : Over X} (g : T ⟶ o₁.A),
        g ≫ (e₁.inv ≫ ψ ≫ e₂.hom) = 1 ↔ (g ≫ e₁.inv) ≫ ψ = 1 := by
      intro T g
      rw [← comp_iso_eq_one e₂ ((g ≫ e₁.inv) ≫ ψ)]
      simp only [Category.assoc]
    refine ⟨?_, ?_⟩
    · rintro g hg ⟨n, hn⟩ y hy
      refine (hk g _).2 ?_
      exact hT1 (g ≫ e₁.inv) ((hz g).1 hg) ⟨n, fun z hz' => (hk g _).1 (hn z hz')⟩ y hy
    · show _ = Ideal.absNorm 𝔴 ^ (D.m * i)
      rw [hm, _root_.one_mul, ← hT2]
      apply Nat.card_congr
      exact
        { toFun := fun g => ⟨g.1 ≫ e₁.inv, (hz g.1).1 g.2.1, fun y hy => (hk g.1 _).1 (g.2.2 y hy)⟩
          invFun := fun g => ⟨g.1 ≫ e₁.hom, (hz _).2 (by simpa using g.2.1),
            fun y hy => (hk _ _).2 (by simpa using g.2.2 y hy)⟩
          left_inv := fun g => Subtype.ext (by simp)
          right_inv := fun g => Subtype.ext (by simp) }

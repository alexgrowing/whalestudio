import Mathlib
import Development.AutomorphicArithmetic.SpecialMaps.QuotObjDefs
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorTypeTjIsogeniesRepresentable

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES GlobalTheory.IwLevel UpperTheory.QO

noncomputable section

namespace UpperTheory.QO.PullIsog

variable {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R] {b : Base D R} {N : ℕ}

private theorem comp_eq_one_iff {S S' : Scheme.{0}} {A A' : Over S} [GrpObj A] [GrpObj A'] {C C' : Over S'}
    [GrpObj C] [GrpObj C'] {f : S' ⟶ S} {u : C.left ⟶ A.left} {v : C'.left ⟶ A'.left}
    (hu : IsGrpPullback C A f u) (hv : IsGrpPullback C' A' f v) {g : A ⟶ A'} {g' : C ⟶ C'}
    (hg : g'.left ≫ v = u ≫ g.left) {T : Over S'} (x : T ⟶ C) :
    x ≫ g' = 1 ↔ pushHom hu T x ≫ g = 1 := by
  have hleftu : (pushHom hu T x).left = x.left ≫ u := rfl
  have hinj : Function.Injective (pushHom hv T) := by
    intro y z hyz
    apply Over.OverMorphism.ext
    apply hv.1.hom_ext
    · exact congrArg Over.Hom.left hyz
    · rw [Over.w y, Over.w z]
  have hpush : pushHom hv T (x ≫ g') = pushHom hu T x ≫ g := by
    apply Over.OverMorphism.ext
    show (x ≫ g').left ≫ v = (pushHom hu T x).left ≫ g.left
    rw [hleftu, Over.comp_left, Category.assoc, hg, Category.assoc]
  constructor
  · intro h1
    rw [← hpush, h1, map_one]
  · intro h1
    apply hinj
    rw [hpush, h1, map_one]

theorem exists_isPIsog_pull {c : ℕ} {T Y : Scheme.{0}} {s₁ : T ⟶ Sp R} {s : Y ⟶ Sp R} {t : T ⟶ Y}
    {o₁ o₁' : Obj b N s₁} {o o' : Obj b N s} (m : ObjMap o₁ o t) (m' : ObjMap o₁' o' t) {ψ : o.A ⟶ o'.A}
    (h : IsPIsog c o o' ψ) :
    ∃ ψ₁ : o₁.A ⟶ o₁'.A, m.φ ≫ ψ.left = ψ₁.left ≫ m'.φ ∧ IsPIsog c o₁ o₁' ψ₁ := by
  obtain ⟨ψ', hq⟩ := h.exists_quasiInv
  obtain ⟨B₁, _, _, θ, ψ₁, ψ₁', _, hpb, hq₁, h1, h2⟩ :=
    GlobalTheory.T.quasiInverseIsogenyPair_baseChange_grpPullback T Y t o.A o'.A c ψ ψ' o₁.A m.φ o'.ab hq m.cart
  obtain ⟨e, he, heθ⟩ := grpPullback_iso hpb m'.cart
  have hψ : m.φ ≫ ψ.left = (ψ₁ ≫ e.hom).left ≫ m'.φ := by
    rw [h1, ← heθ, Over.comp_left, Category.assoc]
  have hψ' : ∀ {W : Scheme} (k : o'.A.left ⟶ W), ψ₁.left ≫ e.hom.left ≫ m'.φ ≫ k = m.φ ≫ ψ.left ≫ k := by
    intro W k
    rw [← Category.assoc m.φ, hψ, Over.comp_left]
    simp only [Category.assoc]
  have hψ0 : ψ₁.left ≫ e.hom.left ≫ m'.φ = m.φ ≫ ψ.left := by
    rw [hψ, Over.comp_left, Category.assoc]
  have ext' : ∀ {Z : Over T} (f g : Z ⟶ o₁'.A), f.left ≫ m'.φ = g.left ≫ m'.φ → f = g :=
    fun f g hfg => Over.OverMorphism.ext (m'.cart.1.hom_ext hfg (by rw [Over.w f, Over.w g]))
  haveI := hq₁.1
  haveI := hq₁.2.1
  haveI := he
  refine ⟨ψ₁ ≫ e.hom, hψ, h.1, inferInstance, ?_, ?_, ?_, e.inv ≫ ψ₁', inferInstance, ?_, ?_⟩
  · intro c'
    apply ext'
    simp only [Over.comp_left, Category.assoc]
    rw [hψ0, m'.act c', hψ', ← Category.assoc (o₁.act.act c').left m.φ, m.act c', Category.assoc]
    congr 1
    have := congrArg Over.Hom.left (h.2.2.1 c')
    simpa only [Over.comp_left, Category.assoc] using this
  · intro y
    apply ext'
    simp only [Over.comp_left, Category.assoc]
    rw [hψ0, m'.eta y, ← Category.assoc (o₁.eta y).left m.φ, m.eta y, Category.assoc]
    congr 1
    have := congrArg Over.Hom.left (h.2.2.2.1 y)
    simpa only [Over.comp_left] using this
  · have hpow₁ : (Hecke.lbPow o₁.P c).IsLB := LB.isLB_linComb o₁.isLB _ _
    have hpull₁ : (o₁'.P.pull (sq2 (ψ₁ ≫ e.hom))).IsLB := pull_isLB o₁'.isLB _
    have e1 : GlobalTheory.CechPic.cls o₁.P o₁.isLB = GlobalTheory.CechPic.pull m.φ₂ (GlobalTheory.CechPic.cls o.P o.isLB) := by
      rw [← GlobalTheory.CechPic.cls_pull o.isLB m.φ₂ (pull_isLB o.isLB _)]
      exact (GlobalTheory.CechPic.cls_eq_iff _ _).mpr m.pol
    have e2 : GlobalTheory.CechPic.cls o₁'.P o₁'.isLB = GlobalTheory.CechPic.pull m'.φ₂ (GlobalTheory.CechPic.cls o'.P o'.isLB) := by
      rw [← GlobalTheory.CechPic.cls_pull o'.isLB m'.φ₂ (pull_isLB o'.isLB _)]
      exact (GlobalTheory.CechPic.cls_eq_iff _ _).mpr m'.pol
    obtain ⟨hpolψ⟩ := h.2.2.2.2.1
    have e3 : GlobalTheory.CechPic.pull (sq2 ψ) (GlobalTheory.CechPic.cls o'.P o'.isLB) = c • GlobalTheory.CechPic.cls o.P o.isLB := by
      rw [← GlobalTheory.CechPic.cls_pull o'.isLB (sq2 ψ) (pull_isLB o'.isLB _),
        ← GlobalTheory.LocTrivDescent.cls_lbPow_eq o.isLB c (LB.isLB_linComb o.isLB _ _)]
      exact ((GlobalTheory.CechPic.cls_eq_iff _ _).mpr hpolψ).symm
    have key : sq2 (ψ₁ ≫ e.hom) ≫ m'.φ₂ = m.φ₂ ≫ sq2 ψ := by
      apply pullback.hom_ext
      · change (sq2 (ψ₁ ≫ e.hom) ≫ m'.φ₂) ≫ (fst o'.A o'.A).left = (m.φ₂ ≫ sq2 ψ) ≫ (fst o'.A o'.A).left
        rw [Category.assoc, m'.sq.1, Category.assoc]
        simp only [sq2]
        rw [← Category.assoc, ← Over.comp_left, lift_fst, ← Over.comp_left, lift_fst, Over.comp_left,
          Over.comp_left, Over.comp_left, Category.assoc, Category.assoc, hψ0, ← Category.assoc,
          ← Category.assoc, m.sq.1]
      · change (sq2 (ψ₁ ≫ e.hom) ≫ m'.φ₂) ≫ (snd o'.A o'.A).left = (m.φ₂ ≫ sq2 ψ) ≫ (snd o'.A o'.A).left
        rw [Category.assoc, m'.sq.2, Category.assoc]
        simp only [sq2]
        rw [← Category.assoc, ← Over.comp_left, lift_snd, ← Over.comp_left, lift_snd, Over.comp_left,
          Over.comp_left, Over.comp_left, Category.assoc, Category.assoc, hψ0, ← Category.assoc,
          ← Category.assoc, m.sq.2]
    refine ⟨(GlobalTheory.CechPic.cls_eq_iff hpow₁ hpull₁).mp ?_⟩
    rw [GlobalTheory.LocTrivDescent.cls_lbPow_eq o₁.isLB c hpow₁, GlobalTheory.CechPic.cls_pull o₁'.isLB _ hpull₁, e1, e2,
      ← GlobalTheory.CechPic.pull_comp, key, GlobalTheory.CechPic.pull_comp, e3, map_nsmul]
  · rw [Category.assoc, Iso.hom_inv_id_assoc]
    exact hq₁.2.2.1
  · rw [Category.assoc, ← Category.assoc ψ₁', hq₁.2.2.2, MonObj.pow_comp, Category.id_comp,
      MonObj.comp_pow, Iso.inv_hom_id]

end UpperTheory.QO.PullIsog

open UpperTheory.QO.PullIsog in
theorem UpperTheory.exists_isPIsog_isTj_of_section_repData :
    ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ), 3 ≤ N → N.Coprime p → ∀ (r : ℤ) (w : Ideal (𝓞 D.F)) (j c : ℕ) (S : Scheme.{0}) (s : S ⟶ Sp R) (o : Obj b N s) (Rd : RepData b N r w j c s o) (σ : S ⟶ Rd.Y.left), σ ≫ Rd.Y.hom = 𝟙 S → ∃ (o'' : Obj b N s) (ψ'' : o.A ⟶ o''.A), IsPIsog c o o'' ψ'' ∧ IsTj r w j o o'' ψ'' ∧ ∀ (T : Over S) (a : T ⟶ o.A), ∃ a₀ : Over.mk (T.hom ≫ σ) ⟶ Rd.o₀.A, a₀.left ≫ Rd.m₀.φ = a.left ∧ (a ≫ ψ'' = 1 ↔ a₀ ≫ Rd.ψ = 1) ∧ ∀ v : Ideal (𝓞 D.F), KilledBy o v a ↔ KilledBy Rd.o₀ v a₀ := by
  intro p _ D R _ b N hN hNp r w j c S s o Rd σ hσ
  let idm : ObjMap o o (𝟙 S) :=
    { φ := 𝟙 _, φ₂ := 𝟙 _, cart := GlobalTheory.SiegLower.isGrpPullback_id o.A, sq := ⟨by simp, by simp⟩,
      act := fun c => by simp, pol := GlobalTheory.SiegLower.lbIso_pull_id o.isLB, eta := fun y => by simp }
  obtain ⟨m', hm'⟩ := IsogRep.exists_factor hN hNp hσ Rd.m₀ idm
  have hs : σ ≫ Rd.Y.hom ≫ s = s := by rw [← Category.assoc, hσ, Category.id_comp]
  obtain ⟨o'', ⟨m''⟩⟩ := IsogRep.exists_pull σ Rd.o' hs
  obtain ⟨ψ'', hsq, hiso⟩ := exists_isPIsog_pull m' m'' Rd.isog
  refine ⟨o'', ψ'', hiso, ?_, fun T a => ?_⟩
  · exact (tjAt_id_iff r w j o o'' ψ'').1
      ((GlobalTheory.T.harrisTaylorType_iff_pulledBack_identity p D R b N _ _ _ _ _ o Rd.o₀ m' o''.A Rd.o'.A m''.φ ψ'' Rd.ψ r w j m''.cart hsq).1
        fun k _ _ _ x _ => Rd.tj k x)
  · refine ⟨pushHom m'.cart T a, ?_, comp_eq_one_iff m'.cart m''.cart hsq.symm a, fun v => ?_⟩
    · change (a.left ≫ m'.φ) ≫ Rd.m₀.φ = a.left
      rw [Category.assoc, hm']
      exact Category.comp_id _
    · unfold GlobalTheory.UPel.HT.ES.KilledBy
      exact forall₂_congr fun x _ => comp_eq_one_iff m'.cart m'.cart (m'.act _) a

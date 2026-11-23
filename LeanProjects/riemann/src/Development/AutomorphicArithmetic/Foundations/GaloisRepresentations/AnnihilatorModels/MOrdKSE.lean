import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.SameNormBasic
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.PulledRead
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.IdealSplit
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FibrePowerMapOfTotalSpacesIsPullbackStatement

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES
open GlobalTheory.IwLevel (InSub IsIsogDeg)
open GlobalTheory.AbDual (evc IsAdditive swap)
attribute [local instance] Ideal.Quotient.field
open UpperTheory.Gal.crystallineComparison UpperTheory.Gal.crystallineComparison.Mod
open GlobalTheory.UPel.HT.EtLev

section
variable {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R] {b : Base D R} {N : ℕ} {M : Model b N} {r : ℤ}
  {w 𝔞 : Ideal (𝓞 D.F)} {j c ρ : ℕ}
  {E : EtModel b N 𝔞 ρ} {π : E.X ⟶ M.X} {mπ : ObjMap E.univ M.univ π} {T : TjD M r w j c}

private theorem pm_hom {S S' : Scheme.{0}} {A' : Over S'} {A : Over S} (f : S' ⟶ S) (φ : A'.left ⟶ A.left)
    (h : φ ≫ A.hom = A'.hom ≫ f) (m : ℕ) :
    GlobalTheory.KS.powMap f φ h m ≫ (GlobalTheory.KS.pow A m).hom = (GlobalTheory.KS.pow A' m).hom ≫ f := by
  unfold GlobalTheory.KS.powMap
  exact Over.w _

private theorem pm_pr {S S' : Scheme.{0}} {A' : Over S'} {A : Over S} (f : S' ⟶ S) (φ : A'.left ⟶ A.left)
    (h : φ ≫ A.hom = A'.hom ≫ f) (m : ℕ) (i : Fin m) :
    GlobalTheory.KS.powMap f φ h m ≫ (GlobalTheory.KS.pr A i).left = (GlobalTheory.KS.pr A' i).left ≫ φ := by
  simp only [GlobalTheory.KS.powMap, GlobalTheory.KS.pr, ← Over.comp_left, Pi.lift_π, Over.homMk_left]

private theorem ksR_hom (L : TjE E mπ T) (k : ℕ) :
    L.ksR k ≫ (GlobalTheory.KS.pow E.univ.A k).hom = (GlobalTheory.KS.pow L.o.A k).hom ≫ L.t := by
  unfold TjE.ksR
  rw [Category.assoc, pm_hom, ← Category.assoc, Over.w]

private theorem ksR_pr (L : TjE E mπ T) (k : ℕ) (i : Fin k) :
    L.ksR k ≫ (GlobalTheory.KS.pr E.univ.A i).left = (GlobalTheory.KS.pr L.o.A i).left ≫ L.ψ.left ≫ L.mt.φ := by
  rw [TjE.ksR, Category.assoc, pm_pr, ← Category.assoc, ← Over.comp_left, Pi.map_π, Over.comp_left, Category.assoc]

private theorem localMap_hom (L : TjE E mπ T) (k : ℕ) :
    L.ksP k ≫ (GlobalTheory.KS.pow E.univ.A k).hom = (GlobalTheory.KS.pow L.o.A k).hom ≫ L.s := pm_hom _ _ _ _

private theorem localMap_projection (L : TjE E mπ T) (k : ℕ) (i : Fin k) :
    L.ksP k ≫ (GlobalTheory.KS.pr E.univ.A i).left = (GlobalTheory.KS.pr L.o.A i).left ≫ L.ms.φ := pm_pr _ _ _ _ _

private theorem ks_pb (L : TjE E mπ T) (k : ℕ) :
    IsPullback (L.ksP k) ((GlobalTheory.KS.pow L.o.A k).hom ≫ L.g) ((GlobalTheory.KS.pow E.univ.A k).hom ≫ π) T.s := by
  rw [TjE.ksP]
  exact (GlobalTheory.T.fibrePowerMapOfTotalSpaces_isPullback _ _ _ _ _ _ _ L.ms.cart.1 k).paste_vert L.pb

private theorem img_of (L : TjE E mπ T) {X : Scheme.{0}} (c : X ⟶ L.o.A.left) (z : X ⟶ T.Y) (a : X ⟶ M.univ.A.left)
    (hz : z = c ≫ L.o.A.hom ≫ L.g) (ha : a = c ≫ L.ms.φ ≫ mπ.φ) (e : a ≫ M.univ.A.hom = z ≫ T.s) :
    T.img z a e = c ≫ L.ψ.left ≫ L.mt.φ ≫ mπ.φ := by
  have key : ∀ hp : IsPullback T.ms.φ T.o.A.hom M.univ.A.hom T.s, hp.lift a z e = c ≫ L.m₀.φ := by
    intro hp
    apply hp.hom_ext
    · rw [hp.lift_fst, Category.assoc, L.tri, ha]
    · rw [hp.lift_snd, Category.assoc, L.m₀.cart.1.w, hz]
  rw [TjD.img, key]
  simp only [Category.assoc]
  rw [← Category.assoc L.m₀.φ, L.sq]
  simp only [Category.assoc]
  rw [L.tri']

end

theorem UpperTheory.Gal.crystallineComparison.Mod.ordKSE_of :
    CorrBC → OrdEmb → PowExt → EtInj → OrdKSE := by
  intro hBC hOE hPE hEI p _ D O _ _ _ _ f b N r w _ hs M ϖ hϖ T 𝔞 ρ E π hπ hfl mπ L k
  have hK : ∀ j : Fin (D.n + 1), KSOKE (L j) k (Nat.card (Gr (𝓞 D.F ⧸ w) (Fin D.n → 𝓞 D.F ⧸ w) (j : ℕ))) := by
    intro j
    obtain ⟨h1, h2, h3⟩ := hBC p D O f b N r w hs M j (Nat.le_of_lt_succ j.isLt) (T j) _ _ _ _ _ (ks_pb (L j) k)
    exact ⟨h1, h2, h3⟩
  have heq : ∀ j, (L j).t ≫ E.s = (L j).s ≫ E.s := by
    intro j
    calc (L j).t ≫ E.s = (L j).t ≫ π ≫ M.s := by rw [hπ]
      _ = (L j).g ≫ (T j).t ≫ M.s := by rw [← Category.assoc, (L j).tπ, Category.assoc]
      _ = (L j).g ≫ (T j).s ≫ M.s := by rw [(T j).st]
      _ = (L j).s ≫ π ≫ M.s := by rw [← Category.assoc, ← (L j).pb.w, Category.assoc]
      _ = (L j).s ≫ E.s := by rw [hπ]
  refine ⟨fun j => Nat.card (Gr (𝓞 D.F ⧸ w) (Fin D.n → 𝓞 D.F ⧸ w) (j : ℕ)), hK, ?_, ?_⟩
  · intro j
    change (L j).ksR k ≫ (GlobalTheory.KS.pow E.univ.A k).hom ≫ E.s = (L j).ksP k ≫ (GlobalTheory.KS.pow E.univ.A k).hom ≫ E.s
    rw [← Category.assoc, ksR_hom, ← Category.assoc ((L j).ksP k), localMap_hom, Category.assoc, Category.assoc, heq j]
  · have hsm : Smooth E.univ.A.hom := @IsAbelianScheme.smooth _ _ _ E.univ.ab
    obtain ⟨hfl', hinj⟩ := hPE E.X E.univ.A k
    have hflat : Flat ((GlobalTheory.KS.pow E.univ.A k).hom ≫ π) := by
      haveI := hfl' hsm
      infer_instance
    have hM : ((GlobalTheory.KS.pow E.univ.A k).hom ≫ π) ≫ M.s = (GlobalTheory.KS.pow E.univ.A k).hom ≫ E.s := by
      rw [Category.assoc, hπ]
    rw [← hM]
    refine hOE p D O f b N r w hs M ϖ hϖ T _ _ hflat (Fin k ⊕ D.La)
      (Sum.elim (fun i => (GlobalTheory.KS.pr E.univ.A i).left ≫ mπ.φ)
        (fun y => (GlobalTheory.KS.pow E.univ.A k).hom ≫ (E.lv y).left ≫ mπ.φ)) ?_ ?_ (fun j => (hK j).corr)
      (fun j => (GlobalTheory.KS.pow (L j).o.A k).hom ≫ (L j).g) (fun j => ks_pb (L j) k) ?_ ?_
    · rintro (i | y)
      · simp only [Sum.elim_inl]
        rw [Category.assoc, mπ.cart.1.w, ← Category.assoc, Over.w]
      · simp only [Sum.elim_inr]
        rw [Category.assoc, Category.assoc, mπ.cart.1.w, ← Category.assoc (E.lv y).left, Over.w]
        simp
    · intro X u v huv hi
      have h0 : u ≫ (GlobalTheory.KS.pow E.univ.A k).hom = v ≫ (GlobalTheory.KS.pow E.univ.A k).hom :=
        hEI p D O b N hs.three hs.cop M 𝔞 ρ E π hπ mπ X _ _ (by simpa [Category.assoc] using huv)
          (fun y => by simpa [Category.assoc] using hi (Sum.inr y))
      apply hinj X u v h0
      intro i
      apply mπ.cart.1.hom_ext
      · simpa [Category.assoc] using hi (Sum.inl i)
      · simp only [Category.assoc, Over.w]
        exact h0
    · intro j
      change (L j).ksR k ≫ (GlobalTheory.KS.pow E.univ.A k).hom ≫ π = ((GlobalTheory.KS.pow (L j).o.A k).hom ≫ (L j).g) ≫ (T j).t
      rw [← Category.assoc, ksR_hom, Category.assoc, (L j).tπ]
      simp only [Category.assoc]
    · intro j i e
      rcases i with i | y
      · have hz : (GlobalTheory.KS.pow (L j).o.A k).hom ≫ (L j).g = (GlobalTheory.KS.pr (L j).o.A i).left ≫ (L j).o.A.hom ≫ (L j).g := by
          rw [← Category.assoc, Over.w]
        have ha : (L j).ksP k ≫ (GlobalTheory.KS.pr E.univ.A i).left ≫ mπ.φ = (GlobalTheory.KS.pr (L j).o.A i).left ≫ (L j).ms.φ ≫ mπ.φ := by
          rw [← Category.assoc, localMap_projection, Category.assoc]
        have hr : (L j).ksR k ≫ (GlobalTheory.KS.pr E.univ.A i).left ≫ mπ.φ = (GlobalTheory.KS.pr (L j).o.A i).left ≫ (L j).ψ.left ≫ (L j).mt.φ ≫ mπ.φ := by
          rw [← Category.assoc, ksR_pr]
          simp only [Category.assoc]
        exact hr.trans (img_of (L j) _ _ _ hz ha e).symm
      · obtain ⟨l, hl⟩ : ∃ l : 𝟙_ (Over (L j).Z) ⟶ (L j).o.A, l.left ≫ (L j).ms.φ = (L j).s ≫ (E.lv y).left := by
          refine ⟨Over.homMk ((L j).ms.cart.1.lift ((L j).s ≫ (E.lv y).left) (𝟙 _) ?_) ?_, ?_⟩
          · rw [Category.assoc, Over.w]
            simp
          · rw [IsPullback.lift_snd]
            simp
          · simp
        have hlev := (L j).lev y l hl
        have hlev' : l.left ≫ (L j).ψ.left ≫ (L j).mt.φ = (L j).t ≫ (E.lv y).left := by
          rw [← Category.assoc, ← Over.comp_left]
          exact hlev
        have hz : (GlobalTheory.KS.pow (L j).o.A k).hom ≫ (L j).g = ((GlobalTheory.KS.pow (L j).o.A k).hom ≫ l.left) ≫ (L j).o.A.hom ≫ (L j).g := by
          rw [Category.assoc, ← Category.assoc l.left, Over.w]
          simp
        have ha : (L j).ksP k ≫ (GlobalTheory.KS.pow E.univ.A k).hom ≫ (E.lv y).left ≫ mπ.φ = ((GlobalTheory.KS.pow (L j).o.A k).hom ≫ l.left) ≫ (L j).ms.φ ≫ mπ.φ := by
          rw [← Category.assoc ((L j).ksP k), localMap_hom]
          simp only [Category.assoc]
          rw [reassoc_of% hl]
        have hr : (L j).ksR k ≫ (GlobalTheory.KS.pow E.univ.A k).hom ≫ (E.lv y).left ≫ mπ.φ = ((GlobalTheory.KS.pow (L j).o.A k).hom ≫ l.left) ≫ (L j).ψ.left ≫ (L j).mt.φ ≫ mπ.φ := by
          rw [← Category.assoc ((L j).ksR k), ksR_hom]
          simp only [Category.assoc]
          rw [reassoc_of% hlev']
        exact hr.trans (img_of (L j) _ _ _ hz ha e).symm

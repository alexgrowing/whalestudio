import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.SameNormBasic
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.IdealSplit
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHarrisTaylorObjectPullbackTer
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorSimilitudeFixingPointEqOne
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES
open GlobalTheory.IwLevel (InSub IsIsogDeg)
open GlobalTheory.AbDual (evc IsAdditive swap)
attribute [local instance] Ideal.Quotient.field
open UpperTheory.Gal.crystallineComparison UpperTheory.Gal.crystallineComparison.Mod

theorem UpperTheory.Gal.crystallineComparison.Mod.tjEEx_of :
    ObjTri → PulledEx → PullKer → UKerW → LevPull → LevPush → TjEEx := by
  intro hTri hPE hPK hUW hLP hLPush p _ D O _ _ _ _ f b N r w _ hS M j c T hF 𝔞 ρ hsup hu E π hπ mπ
  have h3 := hS.three
  have hcop := hS.cop
  obtain ⟨Z, s, g, pb⟩ : ∃ (Z : Scheme.{0}) (s : Z ⟶ E.X) (g : Z ⟶ T.Y), IsPullback s g π T.s :=
    ⟨_, _, _, IsPullback.of_hasPullback π T.s⟩
  obtain ⟨o, ⟨ms⟩⟩ := GlobalTheory.T.exists_harrisTaylorObject_pullback p D O b N E.X Z E.s s E.univ
  obtain ⟨m₁, hm₁⟩ := GlobalTheory.HTQuotRigid.objMap_comp_φ ms mπ
  have hx : (s ≫ π) ≫ M.s = s ≫ E.s := by rw [Category.assoc, hπ]
  obtain ⟨P⟩ := hPE p D O b N h3 hcop M r w j c T Z (s ≫ π) (s ≫ E.s) hx o m₁ g pb.w.symm
  obtain ⟨l, hl, hlm⟩ := hLP p D O b N E.X Z E.s (s ≫ E.s) s E.univ o ms 𝔞 ρ E.lv E.isLev
  have hK : ∀ (X : Over Z) (g' : X ⟶ o.A), UKer r o P.ψ X g' → KilledBy o w g' := by
    rintro X g' ⟨h1, e, h2⟩
    let g₀ : (Over.mk (X.hom ≫ g) : Over T.Y) ⟶ T.o.A := Over.homMk (g'.left ≫ P.m₀.φ) (by
      have hw := P.m₀.cart.1.w
      have hg := Over.w g'
      simp only [Category.assoc, hw, Over.mk_hom]
      rw [← Category.assoc, hg])
    obtain ⟨Ha, -, Hc⟩ := (hPK p D O b N T.Y Z (T.s ≫ M.s) (s ≫ E.s) g T.o T.o' o P.o' P.m₀ P.m' T.ψ P.ψ P.sq).1
      X (Over.mk (X.hom ≫ g)) rfl g' g₀ (by simp [g₀])
    exact (Hc w).2 (hUW p D O f b N r w hS M j c T hF _ g₀ ⟨Ha.1 h1, e, (Hc _).1 h2⟩)
  have hl' := hLPush p D O b N r w 𝔞 ρ hsup hu Z (s ≫ E.s) c o P.o' P.ψ P.isog hK l hl
  obtain ⟨t, ⟨ht, mt, hlev⟩, -⟩ := E.rep Z (s ≫ E.s) P.o' _ hl'
  obtain ⟨n₁, hn₁⟩ := GlobalTheory.HTQuotRigid.objMap_comp_φ mt mπ
  obtain ⟨n₂, hn₂⟩ := GlobalTheory.HTQuotRigid.objMap_comp_φ P.m' T.mt
  have e : t ≫ π = g ≫ T.t := (M.rep Z (s ≫ E.s) P.o').unique
    ⟨by rw [Category.assoc, hπ, ht], ⟨n₁⟩⟩
    ⟨by rw [Category.assoc, ← T.st, ← Category.assoc, ← pb.w, Category.assoc, hπ], ⟨n₂⟩⟩
  have hφ : ∀ (f₁ f₂ : Z ⟶ M.X) (_ : f₁ = f₂) (a : ObjMap P.o' M.univ f₁) (a' : ObjMap P.o' M.univ f₂), a.φ = a'.φ := by
    rintro f₁ _ rfl a a'
    exact (hTri p D O b N h3 hcop Z M.X M.X _ M.s M.s P.o' M.univ M.univ f₁ (𝟙 _)).1 a a'
  refine ⟨{ Z := Z, s := s, t := t, g := g, pb := pb, tπ := e, o := o, o' := P.o', ms := ms, mt := mt, ψ := P.ψ,
            isog := P.isog, tj := P.tj, m₀ := P.m₀, m' := P.m', sq := P.sq, tri := P.tri.trans hm₁,
            tri' := hn₂.symm.trans ((hφ _ _ e.symm n₂ n₁).trans hn₁), lev := ?_ }⟩
  intro y l' hl''
  have hll : l' = l y := by
    apply Over.OverMorphism.ext
    apply ms.cart.1.hom_ext
    · rw [hl'', hlm]
    · rw [Over.w l', Over.w (l y)]
  subst hll
  exact hlev y

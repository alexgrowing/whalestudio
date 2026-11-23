import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.FiniteEtaleModels.SecInjG
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.IdealSplit
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGluedCommGroupSchemeArtinFibreProduct

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.UPel.HT.EtLev GlobalTheory.LKTrip GlobalTheory.LKGeo
open UpperTheory.Gal.Int.Geo
open UpperTheory.Gal.crystallineComparison.Mod (Std TjD KerAt)
open scoped TensorProduct
open UpperTheory.Gal.FiniteEtaleModels

namespace UpperTheory.Gal.FiniteEtaleModels

section
variable {S S' : Scheme.{0}} {G' : Over S'} [GrpObj G'] {G : Over S} [GrpObj G] {f : S' ⟶ S} {φ : G'.left ⟶ G.left}

private theorem pt_one_iff (h : IsGrpPullback G' G f φ) {T : Over S'} (x : T ⟶ G') (x₀ : Over.mk (T.hom ≫ f) ⟶ G)
    (e : x₀.left = x.left ≫ φ) : x = 1 ↔ x₀ = 1 := by
  constructor
  · rintro rfl
    exact Over.OverMorphism.ext (by rw [e, GlobalTheory.GlueGrpLaw.one_left h T])
  · intro h0
    refine Over.OverMorphism.ext (h.1.hom_ext ?_ ?_)
    · rw [← e, h0, GlobalTheory.GlueGrpLaw.one_left h T]
    · rw [Over.w x, Over.w (1 : T ⟶ G')]

end

section
variable {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R] {b : Base D R} {N : ℕ} {M : Model b N} {r : ℤ}
  {w : Ideal (𝓞 D.F)} {j c : ℕ}

private theorem kerAt_lift (T : TjD M r w j c) {X : Scheme.{0}} (z : X ⟶ T.Y) (a' : Over.mk z ⟶ T.o.A) :
    KerAt T z (a'.left ≫ T.ms.φ) ↔ a' ≫ T.ψ = 1 := by
  refine ⟨fun h => h a' rfl, fun h b hb => ?_⟩
  have : b = a' := Over.OverMorphism.ext (T.ms.cart.1.hom_ext hb (by rw [Over.w b, Over.w a']))
  rw [this]; exact h

end

section
variable {p : ℕ} [Fact p.Prime] {D : Datum p} {G : HTGroup p} {L : Link D G} {E : Type} [Field E] [NumberField E] {gb : GBase D.toG E}
  {w : HeightOneSpectrum (𝓞 E)} {q : ℕ} [Fact q.Prime] {r : ℤ} {𝔴 𝔫 : Ideal (𝓞 D.F)} {S : Site gb w q r 𝔴 𝔫} {k : ℕ} {T : KS L gb k}
  {N₀ : ℕ} {𝔟₁ 𝔟₂ : Ideal (𝓞 D.F)} {X₁ : Ext S N₀ 𝔟₁} {X₂ : Ext S N₀ 𝔟₂} {𝔴' : Ideal (𝓞 D.F)} {i : ℕ} {h : G.GAf} {M₁ M₂ : Lv p}
  {c₁ c₂ : ℕ} {a₁ a₂ : 𝓞 D.F}

private theorem ker_read {C₁ : X₁.site.Cl (T.M M₁).univ c₁ a₁} {C₂ : X₂.site.Cl (T.M M₂).univ c₂ a₂} {W : Wit T h M₁ M₂}
    {f : X₁.Y.X ⟶ X₂.M.X} {mf : ObjMap X₁.Y.univ X₂.M.univ f} {c : ℕ} {Tj : TjD X₂.M r 𝔴' i c} (P : BPt C₁ C₂ W mf Tj)
    {Ω : Type} [Field Ω] (z : Sp Ω ⟶ (T.M M₁).X) (e : 𝟙_ (Over (T.M M₁).X) ⟶ (T.M M₁).univ.A) :
    KerAt Tj (z ≫ P.y) (z ≫ e.left ≫ C₁.m.φ ≫ mf.φ) ↔ toUnit (Over.mk z) ≫ e ≫ W.ψ = 1 := by
  let a' : Over.mk (z ≫ P.y) ⟶ Tj.o.A := Over.homMk (z ≫ e.left ≫ P.fa) (by
    have h1 : e.left ≫ (T.M M₁).univ.A.hom = 𝟙 _ := Over.w e
    simp only [Over.mk_hom, Category.assoc]
    rw [P.ca.1.w, reassoc_of% h1])
  have h1 := kerAt_lift Tj (z ≫ P.y) a'
  have h2 : a'.left ≫ Tj.ms.φ = z ≫ e.left ≫ C₁.m.φ ≫ mf.φ := by
    simp only [a', Over.homMk_left, Category.assoc, P.ms]
  rw [h2] at h1
  rw [h1]
  refine (pt_one_iff P.cb (toUnit (Over.mk z) ≫ e ≫ W.ψ) (a' ≫ Tj.ψ) ?_).symm
  simp only [a', Over.comp_left, Over.homMk_left, Category.assoc, P.sq]
  simp

end

section
variable {q : ℕ} [Fact q.Prime] {D : Datum q} {R R' : Type} [CommRing R] [CommRing R'] [Algebra ℚ R'] {b : Base D R} {gb : GBase D.toG R'}
  {N₀ N₁ : ℕ} {𝔟 𝔴' : Ideal (𝓞 D.F)}

private theorem cls_read (hb : 𝔟 ≤ 𝔴') (Y : EtModel b N₀ 𝔟 1) (M : Model b N₀) {f : Y.X ⟶ M.X} (mf : ObjMap Y.univ M.univ f)
    {X : Scheme.{0}} {s : X ⟶ Sp R'} {o : GObj gb N₁ s} {β : R →+* R'} {c : ℕ} {a : 𝓞 D.F} (C : Cls Y β o c a)
    {Ω : Type} [Field Ω] [IsAlgClosed Ω] (x : Sp Ω ⟶ X) (g : Over.mk ((x ≫ C.j) ≫ f) ⟶ M.univ.A)
    (hg : ES.KilledBy M.univ 𝔴' g) :
    ∃ d : D.La, ∀ z : Sp Ω ⟶ X, z ≫ C.j = x ≫ C.j → g.left = z ≫ (o.eta d).left ≫ C.m.φ ≫ mf.φ := by
  let g₁ : Over.mk (x ≫ C.j) ⟶ Y.univ.A :=
    Over.homMk (mf.cart.1.lift g.left (x ≫ C.j) (Over.w g)) (by simp)
  have hg₁ : g₁.left ≫ mf.φ = g.left := by simp [g₁]
  have hk : ∀ c ∈ 𝔟 ^ 1, g₁ ≫ Y.univ.act.act (algebraMap (𝓞 D.F) D.O c) = 1 := fun c hc => by
    refine (pt_one_iff mf.cart _ (g ≫ M.univ.act.act (algebraMap (𝓞 D.F) D.O c)) ?_).2 (hg c (hb (by simpa using hc)))
    simp only [Over.comp_left, Category.assoc]
    rw [mf.act, ← Category.assoc, hg₁]
  obtain ⟨y, hy⟩ := (Y.isLev.2.2.2 Ω (x ≫ C.j)).2 g₁ hk
  refine ⟨algebraMap (𝓞 D.F) D.O a • y, fun z hz => ?_⟩
  have hl := C.lv y
  rw [← hg₁, ← hy, reassoc_of% hl, reassoc_of% hz]
  simp [Over.toUnit_left]

end

end UpperTheory.Gal.FiniteEtaleModels

theorem UpperTheory.Gal.FiniteEtaleModels.bKer_of :
    SecInjG → TrEtaPt → BKer := by
  intro hS hT p _ D G L hSc E _ _ gb w q _ r 𝔴 𝔫 S k T N₀ 𝔟₁ 𝔟₂ X₁ X₂ 𝔴' i hmax hu hb hi h hint htj M₁ M₂ c₁ c₂ a₁ a₂ hn₁ hn₂ C₁ C₂ W f mf hf
    e he hpos Tj P Ω _ _ x x' hxx'
  haveI : CharZero Ω :=
    charZero_of_injective_ringHom (Spec.preimage (x ≫ (T.M M₁).s)).hom.injective
  have hb' : 𝔟₁ ≤ 𝔴' := hb.trans Ideal.mul_le_right
  refine hS q (datAt S.atq S.sp) (Ow w) S.b N₀ X₂.lev.1 X₂.lev.2.1 hSc.m1 r 𝔴' i e hmax hu hi hpos X₂.M Tj Ω ((x ≫ C₁.j) ≫ f)
    (x ≫ P.y) (x' ≫ P.y) ?_ ?_ ?_
  · rw [Category.assoc, Category.assoc, P.ys]
  · rw [Category.assoc, P.ys, ← Category.assoc, hxx', Category.assoc]
  intro g hg
  obtain ⟨d, hd⟩ := cls_read (D := datAt S.atq S.sp) hb' X₁.Y X₂.M mf C₁ x g hg
  have k₁ : KerAt Tj (x ≫ P.y) g.left ↔ toUnit (Over.mk x) ≫ (T.M M₁).univ.eta d ≫ W.ψ = 1 := by
    rw [hd x rfl]; exact ker_read P x _
  have k₂ : KerAt Tj (x' ≫ P.y) g.left ↔ toUnit (Over.mk x') ≫ (T.M M₁).univ.eta d ≫ W.ψ = 1 := by
    rw [hd x' hxx'.symm]; exact ker_read P x' _
  exact k₁.trans (((hT p D G L E gb h (T.M M₁).X (T.M M₁).s M₁ M₂ (T.M M₁).univ W.o W.ψ W.trans Ω x d).1.trans
    (hT p D G L E gb h (T.M M₁).X (T.M M₁).s M₁ M₂ (T.M M₁).univ W.o W.ψ W.trans Ω x' d).1.symm).trans k₂.symm)

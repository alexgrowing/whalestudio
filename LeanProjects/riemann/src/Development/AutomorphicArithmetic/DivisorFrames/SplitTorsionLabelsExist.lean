import Development.AutomorphicArithmetic.LocalEmbeddings.RootFrame
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.LocallyOfFiniteTypeKer
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ObjIsAbelianSchemeDimRigidifiedSym
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsPushEquiv
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsSpecialisationWithThetaPoint
open CategoryTheory AlgebraicGeometry NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.BasicNotions Formalism.L2.Pj GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.Mean4O GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.TrivFlag GlobalTheory.LineNorm
open Formalism.MainNotions.DIV.Cons (intO)
open scoped TensorProduct Matrix
open MonObj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.RootFrame

private theorem epi_sp {k K : Type} [Field k] [Field K] (a : k →+* K) : Epi (spMap a) := by
  letI := a.toAlgebra
  have h1 : Flat (spMap a) := by
    rw [HasRingHomProperty.Spec_iff (P := @Flat)]
    exact (inferInstance : Module.Flat k K)
  have h2 : Surjective (spMap a) := ⟨fun y => ⟨IsLocalRing.closedPoint K, Subsingleton.elim (α := PrimeSpectrum k) _ _⟩⟩
  exact Flat.epi_of_flat_of_surjective _

private theorem weil_desc {S : Scheme.{0}} (P : Out.PolAV S) {K Ω : Type} [Field K] [Field Ω] (io : K →+* Ω)
    {y : Sp K ⟶ S} {y' : Sp Ω ⟶ S} (h : Over.mk y' ⟶ Over.mk y) (hl : h.left = spMap io) (q : ℕ)
    (σ σ' : Over.mk y ⟶ P.A) (hσ : σ ^ q = 1) (hσ' : σ' ^ q = 1) (τ τ' : Over.mk y' ⟶ P.A) (e : h ≫ σ = τ)
    (e' : h ≫ σ' = τ') (v : Kˣ) (hv : Out.WeilIs P.A P.L (q : ℤ) τ τ' (unitOn (Units.map (io : K →* Ω) v))) :
    Out.WeilIs P.A P.L (q : ℤ) σ σ' (unitOn v) := by
  subst e e'
  obtain ⟨cq, hcq, -⟩ := GlobalTheory.LevelCompare.weil_existsUnique P q σ σ' hσ hσ'
  obtain ⟨u, rfl⟩ := GlobalTheory.Ex.Specialise.unitOn_bijective.2 cq
  have hN := (GlobalTheory.LevelCompare.weil_skew_natural P q (Over.mk y)).2 (Over.mk y') h σ σ' (unitOn u) hcq
  rw [hl, GlobalTheory.Ex.Specialise.map_unitOn] at hN
  have hu := GlobalTheory.Ex.Specialise.unitOn_bijective.1
    ((GlobalTheory.LevelCompare.weil_existsUnique P q (h ≫ σ) (h ≫ σ') (by rw [← MonObj.comp_pow, hσ, MonObj.comp_one])
      (by rw [← MonObj.comp_pow, hσ', MonObj.comp_one])).unique hN hv)
  rw [← Units.map_injective io.injective hu]
  exact hcq

theorem UpperTheory.split_torsion_labels_exist :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (Z : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model Xo c (algebraMap (𝓞 c.F) c.F)) (K : Type) [Field K] [CharZero K] (y : Sp K ⟶ Xo.XF c) (q : ℕ), q ≠ 0 → (∃ ζ : K, IsPrimitiveRoot ζ q) → GlobalTheory.HtGen.SplitK Z.t (y ≫ Z.j) q → ∃ (lb : Dw.La → (Over.mk y ⟶ Z.oF.t.G)) (ζ : Kˣ), IsLabel Z y q lb ζ ∧ ∃ χ : Dw.La → (GlobalTheory.HtGen.TorsK Z.t (y ≫ Z.j) q →* Kˣ), ∀ a b (k : GlobalTheory.HtGen.TorsK Z.t (y ≫ Z.j) q), k.1.left = (lb b).left ≫ Z.m.φ → χ a k = ζ ^ Dw.EF a b := by
  intro E _ _ _ H Dw l Xo c Z K _ _ y q hq ⟨ζ₀, hζ₀⟩ hs
  classical
  have hq0 : 0 < q := Nat.pos_of_ne_zero hq
  haveI : NeZero q := ⟨hq⟩
  let Ω := AlgebraicClosure K
  let io : K →+* Ω := algebraMap K Ω
  haveI := epi_sp io
  let y' : Sp Ω ⟶ Xo.XF c := spMap io ≫ y
  obtain ⟨β₀, hβ₀⟩ : ∃ β₀ : KA l →+* Ω, y' ≫ (Limits.pullback.fst _ _ ≫ Xo.s) = spMap β₀ :=
    ⟨(Spec.preimage (y' ≫ (Limits.pullback.fst _ _ ≫ Xo.s))).hom, by simp [spMap]⟩
  obtain ⟨-, I, -⟩ := Z.oF.geom Ω y' β₀ hβ₀
  let h : Over.mk y' ⟶ Over.mk y := Over.homMk (spMap io) rfl
  have hl : h.left = spMap io := rfl
  obtain ⟨e, he⟩ := GlobalTheory.LiePull.exists_pushEquiv Z.m.cart (Over.mk y) (y ≫ Z.j) rfl
  obtain ⟨e', he'⟩ := GlobalTheory.LiePull.exists_pushEquiv Z.m.cart (Over.mk y') (spMap io ≫ y ≫ Z.j)
    (Category.assoc _ _ _).symm
  have hinj : ∀ σ σ' : Over.mk y ⟶ Z.oF.t.G, h ≫ σ = h ≫ σ' → σ = σ' := by
    intro σ σ' hh
    apply Over.OverMorphism.ext
    have := congrArg (fun z => z.left) hh
    simp only [Over.comp_left, hl] at this
    exact (cancel_epi (spMap io)).1 this
  have hex : ∀ τ : Over.mk y' ⟶ Z.oF.t.G, τ ^ q = 1 → ∃ σ : Over.mk y ⟶ Z.oF.t.G, h ≫ σ = τ := by
    intro τ hτ
    obtain ⟨w₀, hw₀⟩ := hs Ω io (e' τ) (by rw [← map_pow, hτ, map_one])
    have hw : w₀ ≫ Z.t.G.hom = y ≫ Z.j := by
      rw [← cancel_epi (spMap io), ← Category.assoc, hw₀]
      exact Over.w (e' τ)
    let w : Over.mk (y ≫ Z.j) ⟶ Z.t.G := Over.homMk w₀ hw
    refine ⟨e.symm w, e'.injective (Over.OverMorphism.ext ?_)⟩
    rw [he', ← hw₀, Over.comp_left, Category.assoc, ← he, MulEquiv.apply_symm_apply]
    rfl
  have hev : ∀ a, I.ev q a ^ q = 1 := fun a => (I.onto q hq0 _).2 ⟨a, rfl⟩
  choose lb hlb using fun a => hex (I.ev q a) (hev a)
  have htor : ∀ σ : Over.mk y ⟶ Z.oF.t.G, σ ^ q = 1 ↔ (h ≫ σ) ^ q = 1 := by
    intro σ
    rw [← MonObj.comp_pow]
    refine ⟨fun hσ => by rw [hσ, MonObj.comp_one], fun hσ => hinj _ _ (by rw [hσ, MonObj.comp_one])⟩
  have hlt : ∀ a, lb a ^ q = 1 := fun a => by rw [htor, hlb]; exact hev a
  have hmi : Function.Injective (Units.map (io : K →* Ω)) := Units.map_injective io.injective
  obtain ⟨ζ, hζ⟩ : ∃ ζ : Kˣ, Units.map (io : K →* Ω) ζ = I.ζ q := by
    have h1 : IsPrimitiveRoot (io ζ₀) q := hζ₀.map_of_injective io.injective
    obtain ⟨i, -, hi⟩ := h1.eq_pow_of_pow_eq_one (ξ := (I.ζ q : Ω))
      (by rw [← Units.val_pow_eq_pow_val, (I.ζ_prim q hq0).pow_eq_one, Units.val_one])
    refine ⟨(hζ₀.isUnit hq).unit ^ i, Units.ext ?_⟩
    rw [← hi]
    simp
  let P := GlobalTheory.Obj.toPolAV Z.oF
  have hadd : ∀ a b, lb (a + b) = lb a * lb b := fun a b =>
    hinj _ _ (by rw [MonObj.comp_mul, hlb, hlb, hlb, I.add])
  have honto : ∀ σ : Over.mk y ⟶ Z.oF.t.G, σ ^ q = 1 ↔ ∃ a, lb a = σ := by
    intro σ
    refine ⟨fun hσ => ?_, by rintro ⟨a, rfl⟩; exact hlt a⟩
    obtain ⟨a, ha⟩ := (I.onto q hq0 _).1 ((htor σ).1 hσ)
    exact ⟨a, hinj _ _ (by rw [hlb, ha])⟩
  have hweil : ∀ a b, Out.WeilIs Z.oF.t.G Z.oF.t.PP.L (q : ℤ) (lb a) (lb b) (unitOn (ζ ^ Dw.EF a b)) := by
    intro a b
    refine weil_desc P io h hl q (lb a) (lb b) (hlt a) (hlt b) (I.ev q a) (I.ev q b) (hlb a) (hlb b) _ ?_
    have hz : Units.map (io : K →* Ω) (ζ ^ Dw.EF a b) = I.ζ q ^ Dw.EF a b := by rw [map_zpow, hζ]
    rw [hz]
    exact I.isom q hq0 a b
  have hwd : ∀ a b b', lb b = lb b' → ζ ^ Dw.EF a b = ζ ^ Dw.EF a b' := by
    intro a b b' hb
    have h2 := hweil a b'
    rw [← hb] at h2
    exact GlobalTheory.Ex.Specialise.unitOn_bijective.1
      ((GlobalTheory.LevelCompare.weil_existsUnique P q (lb a) (lb b) (hlt a) (hlt b)).unique (hweil a b) h2)
  have hk : ∀ k : GlobalTheory.HtGen.TorsK Z.t (y ≫ Z.j) q, ∃ b, lb b = e.symm k.1 := fun k =>
    (honto _).1 (by
      have hk1 : k.1 ^ q = 1 := k.2
      rw [← map_pow, hk1, map_one])
  choose bk hbk using hk
  refine ⟨lb, ζ, ⟨?_, hadd, ?_, honto, hweil⟩, fun a => MonoidHom.mk' (fun k => ζ ^ Dw.EF a (bk k)) ?_, ?_⟩
  · refine IsPrimitiveRoot.of_map_of_injective (f := Units.map (io : K →* Ω)) ?_ hmi
    rw [hζ]; exact I.ζ_prim q hq0
  · intro o a
    refine hinj _ _ ?_
    rw [← Category.assoc, hlb, hlb]
    exact I.lin q o a
  · intro k k'
    rw [← zpow_add, ← map_add]
    refine hwd _ _ _ ?_
    exact (hbk (k * k')).trans ((map_mul e.symm k.1 k'.1).trans
      ((congrArg₂ (· * ·) (hbk k) (hbk k')).symm.trans (hadd _ _).symm))
  · intro a b k hkb
    refine hwd _ _ _ ?_
    rw [hbk, MulEquiv.symm_apply_eq]
    apply Over.OverMorphism.ext
    rw [he]
    exact hkb

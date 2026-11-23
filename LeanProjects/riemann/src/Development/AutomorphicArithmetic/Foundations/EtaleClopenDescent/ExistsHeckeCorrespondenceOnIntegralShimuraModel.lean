import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsTjCorrDiagModel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteEtaleTjCorrespondencePInvertibleStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHarrisTaylorObjectPullbackBis
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorObjectMapsComposeCancel
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsQProjOverBaseChangeAndFiniteRestrict
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES

noncomputable section

namespace UpperTheory.Cb.isogenyLiftUniqueness

variable {p : ℕ} [Fact p.Prime] {D : Datum p} {R R' : Type} [CommRing R] [CommRing R'] {N : ℕ} {S : Scheme.{0}}

private theorem sp_surj {A B : Type} [CommRing A] [CommRing B] (u : Sp B ⟶ Sp A) :
    ∃ β : A →+* B, u = spMap β :=
  ⟨(Spec.preimage u).hom, by simp [spMap]⟩

private theorem sp_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap g ≫ spMap f = spMap (g.comp f) := by
  simp only [spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]

private theorem sp_inj {A B : Type} [CommRing A] [CommRing B] {f g : A →+* B} (h : spMap f = spMap g) : f = g :=
  congrArg CommRingCat.Hom.hom (Spec.map_injective h)

private def baseMap (b : Base D R) (φ : R →+* R') (hp : IsUnit ((p : ℕ) : R')) : Base D R' where
  unit k hk := by
    have h := (b.unit k hk).map φ
    rwa [map_natCast] at h
  ρ := φ b.ρ
  ρ_root := by
    have h := congrArg φ b.ρ_root
    simpa using h
  t i := φ.comp (b.t i)
  t_ω i := by simp [b.t_ω]
  comax i j hij := by
    have h := congrArg (Ideal.map φ) (b.comax i j hij)
    rw [Ideal.map_span, Ideal.map_top] at h
    rw [eq_top_iff, ← h]
    apply Ideal.span_mono
    rintro _ ⟨_, ⟨x, rfl⟩, rfl⟩
    exact ⟨x, by simp⟩
  apart i j hij k _ _ β := by
    exfalso
    have h := hp.map β
    rw [map_natCast, CharP.cast_eq_zero k p] at h
    exact not_isUnit_zero h

variable {b : Base D R} {φ : R →+* R'} {hp : IsUnit ((p : ℕ) : R')}

private def toR {t : S ⟶ Sp R'} {s : S ⟶ Sp R} (h : t ≫ spMap φ = s) (o : Obj (baseMap b φ hp) N t) :
    Obj b N s where
  A := o.A
  ab := o.ab
  act := o.act
  P := o.P
  isLB := o.isLB
  rig₁ := o.rig₁
  rig₂ := o.rig₂
  symm := o.symm
  ample := o.ample
  kerP := o.kerP
  rosati := o.rosati
  lie R₁ _ β x hx v hv := by
    obtain ⟨β', hβ'⟩ := sp_surj (x ≫ t)
    obtain rfl : β = β'.comp φ := sp_inj (by rw [← hx, ← h, ← Category.assoc, hβ', sp_comp])
    exact o.lie R₁ β' x hβ' v hv
  lieRank k _ _ x β hx i := by
    obtain ⟨β', hβ'⟩ := sp_surj (x ≫ t)
    obtain rfl : β = β'.comp φ := sp_inj (by rw [← hx, ← h, ← Category.assoc, hβ', sp_comp])
    exact o.lieRank k x β' hβ' i
  eta := o.eta
  eta_add := o.eta_add
  eta_lin := o.eta_lin
  eta_ker := o.eta_ker
  geom k _ _ x β hx := by
    obtain ⟨β', hβ'⟩ := sp_surj (x ≫ t)
    obtain rfl : β = β'.comp φ := sp_inj (by rw [← hx, ← h, ← Category.assoc, hβ', sp_comp])
    exact o.geom k x β' hβ'

private def ofR {t : S ⟶ Sp R'} {s : S ⟶ Sp R} (h : t ≫ spMap φ = s) (o : Obj b N s) :
    Obj (baseMap b φ hp) N t where
  A := o.A
  ab := o.ab
  act := o.act
  P := o.P
  isLB := o.isLB
  rig₁ := o.rig₁
  rig₂ := o.rig₂
  symm := o.symm
  ample := o.ample
  kerP := o.kerP
  rosati := o.rosati
  lie R₁ _ β x hx v hv := o.lie R₁ (β.comp φ) x (by rw [← h, ← Category.assoc, hx, sp_comp]) v hv
  lieRank k _ _ x β hx i := o.lieRank k x (β.comp φ) (by rw [← h, ← Category.assoc, hx, sp_comp]) i
  eta := o.eta
  eta_add := o.eta_add
  eta_lin := o.eta_lin
  eta_ker := o.eta_ker
  geom k _ _ x β hx := o.geom k x (β.comp φ) (by rw [← h, ← Category.assoc, hx, sp_comp])

local macro "cp " m:term:max : term =>
  `(⟨($m).φ, ($m).φ₂, ($m).cart, ($m).sq, ($m).act, ($m).pol, ($m).eta⟩)

private theorem mem_basicOpen {X T : Scheme.{0}} (g : T ⟶ X) (hu : IsUnit ((p : ℕ) : Γ(T, ⊤))) (z : T) :
    g z ∈ X.basicOpen ((p : ℕ) : Γ(X, ⊤)) := by
  have h : g ⁻¹ᵁ X.basicOpen ((p : ℕ) : Γ(X, ⊤)) = ⊤ := by
    rw [Scheme.preimage_basicOpen, map_natCast]
    exact T.basicOpen_of_isUnit hu
  have hz : z ∈ g ⁻¹ᵁ X.basicOpen ((p : ℕ) : Γ(X, ⊤)) := by
    rw [h]; trivial
  exact hz

private theorem exists_lift {X T : Scheme.{0}} (g : T ⟶ X) (hu : IsUnit ((p : ℕ) : Γ(T, ⊤))) :
    ∃ f : T ⟶ (X.basicOpen ((p : ℕ) : Γ(X, ⊤))).toScheme, f ≫ (X.basicOpen ((p : ℕ) : Γ(X, ⊤))).ι = g := by
  refine ⟨IsOpenImmersion.lift _ g ?_, IsOpenImmersion.lift_fac _ _ _⟩
  rintro _ ⟨z, rfl⟩
  rw [Scheme.Opens.range_ι]
  exact mem_basicOpen g hu z

private theorem isUnit_of_sp {T : Scheme.{0}} (t : T ⟶ Sp R') (hp : IsUnit ((p : ℕ) : R')) :
    IsUnit ((p : ℕ) : Γ(T, ⊤)) := by
  have h := hp.map ((Scheme.ΓSpecIso (CommRingCat.of R')).inv ≫ t.appTop).hom
  rwa [map_natCast] at h

private abbrev Rp (p : ℕ) (R : Type) [CommRing R] : Type := Localization.Away ((p : ℕ) : R)

private abbrev πp (p : ℕ) (R : Type) [CommRing R] : Sp (Rp p R) ⟶ Sp R := spMap (algebraMap R (Rp p R))

private instance : IsOpenImmersion (πp p R) := by
  unfold πp spMap
  infer_instance

private theorem isUnit_Rp : IsUnit ((p : ℕ) : Rp p R) := by
  have h := IsLocalization.Away.algebraMap_isUnit (S := Rp p R) ((p : ℕ) : R)
  rwa [map_natCast] at h

private theorem opensRange_πp :
    (πp p R).opensRange = (Sp R).basicOpen ((p : ℕ) : Γ(Sp R, ⊤)) := by
  have h := basicOpen_eq_of_affine (R := CommRingCat.of R) ((p : ℕ) : R)
  rw [map_natCast] at h
  rw [h]
  apply SetLike.coe_injective
  exact PrimeSpectrum.localization_away_comap_range (Rp p R) ((p : ℕ) : R)

private theorem preimage_bo {X : Scheme.{0}} (s : X ⟶ Sp R) :
    s ⁻¹ᵁ (Sp R).basicOpen ((p : ℕ) : Γ(Sp R, ⊤)) = X.basicOpen ((p : ℕ) : Γ(X, ⊤)) := by
  rw [Scheme.preimage_basicOpen, map_natCast]
  rfl

private abbrev bb (b : Base D R) : Base D (Rp p R) := baseMap b (algebraMap R (Rp p R)) isUnit_Rp

private abbrev Uo {b : Base D R} (M : Model b N) : M.X.Opens := M.X.basicOpen ((p : ℕ) : Γ(M.X, ⊤))

private theorem range_sU {b : Base D R} (M : Model b N) :
    Set.range ((Uo M).ι ≫ M.s) ⊆ Set.range (πp p R) := by
  rintro _ ⟨z, rfl⟩
  have h1 : (Uo M).ι z ∈ M.s ⁻¹ᵁ (Sp R).basicOpen ((p : ℕ) : Γ(Sp R, ⊤)) := by
    rw [preimage_bo]
    have h2 : (Uo M).ι z ∈ Set.range (Uo M).ι := ⟨z, rfl⟩
    rwa [Scheme.Opens.range_ι] at h2
  have h3 : M.s ((Uo M).ι z) ∈ (πp p R).opensRange := by
    rw [opensRange_πp]
    exact h1
  simpa using h3

private def sU {b : Base D R} (M : Model b N) : (Uo M).toScheme ⟶ Sp (Rp p R) :=
  IsOpenImmersion.lift (πp p R) ((Uo M).ι ≫ M.s) (range_sU M)

private theorem sU_fac {b : Base D R} (M : Model b N) : sU M ≫ πp p R = (Uo M).ι ≫ M.s :=
  IsOpenImmersion.lift_fac _ _ _

private theorem pbU {b : Base D R} (M : Model b N) : IsPullback (Uo M).ι (sU M) M.s (πp p R) :=
  (IsOpenImmersion.isPullback (sU M) (Uo M).ι (πp p R) M.s (sU_fac M).symm
    (by rw [opensRange_πp, preimage_bo, Scheme.Opens.opensRange_ι])).flip

private theorem exists_uO {b : Base D R} (M : Model b N) :
    ∃ o : Obj b N ((Uo M).ι ≫ M.s), Nonempty (ObjMap o M.univ (Uo M).ι) :=
  GlobalTheory.HTPull.exists_objMap_pull p D R b N _ _ M.s (Uo M).ι M.univ

private def uO {b : Base D R} (M : Model b N) : Obj b N ((Uo M).ι ≫ M.s) := (exists_uO M).choose

private def uM {b : Base D R} (M : Model b N) : ObjMap (uO M) M.univ (Uo M).ι := (exists_uO M).choose_spec.some

private def mdl {b : Base D R} (M : Model b N) : Model (bb (p := p) b) N where
  X := (Uo M).toScheme
  s := sU M
  qproj := GlobalTheory.isQProjOver_of_isPullback_spMap _ (pbU M) M.qproj
  smooth := (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback (pbU M) M.smooth
  univ := ofR (sU_fac M) (uO M)
  rep S t o := by
    obtain ⟨g, ⟨hg, ⟨mg⟩⟩, huq⟩ := M.rep S (t ≫ πp p R) (toR rfl o)
    obtain ⟨f, rfl⟩ := exists_lift g (isUnit_of_sp t isUnit_Rp)
    obtain ⟨m⟩ := MapComp.cancel mg (uM M)
    refine ⟨f, ⟨?_, ⟨cp m⟩⟩, ?_⟩
    · rw [← cancel_mono (πp p R), Category.assoc, sU_fac, ← Category.assoc]
      exact hg
    · rintro f' ⟨hf', ⟨m'⟩⟩
      have m'' : ObjMap (toR (φ := algebraMap R (Rp p R)) rfl o) (uO M) f' := cp m'
      have e : f' ≫ (Uo M).ι = f ≫ (Uo M).ι := huq (f' ≫ (Uo M).ι)
        ⟨by rw [Category.assoc, ← sU_fac, ← Category.assoc, hf'], ⟨MapComp.comp m'' (uM M)⟩⟩
      exact (cancel_mono (Uo M).ι).1 e

private theorem main {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R] [IsNoetherianRing R] {b : Base D R} {N : ℕ}
    (hN : 3 ≤ N) (hNp : N.Coprime p) {r : ℤ} {w : Ideal (𝓞 D.F)} {j c : ℕ} (hw : w.IsMaximal)
    (hu : uIdeal D r ≤ w) (hj : j ≤ D.n) (hc : ∃ e : ℕ, c = p ^ e ∧ (0 < j → 0 < e)) (hm : D.m = 1)
    (M : Model b N) :
    ∃ (Y₀ : Scheme.{0}) (s₀ t₀ : Y₀ ⟶ M.X) (gs gt : Y₀ ⟶ (M.X.basicOpen ((p : ℕ) : Γ(M.X, ⊤))).toScheme) (o₀ o₀' : Obj b N (s₀ ≫ M.s)) (ms₀ : ObjMap o₀ M.univ s₀) (mt₀ : ObjMap o₀' M.univ t₀) (ψ₀ : o₀.A ⟶ o₀'.A), s₀ ≫ M.s = t₀ ≫ M.s ∧ gs ≫ (M.X.basicOpen ((p : ℕ) : Γ(M.X, ⊤))).ι = s₀ ∧ gt ≫ (M.X.basicOpen ((p : ℕ) : Γ(M.X, ⊤))).ι = t₀ ∧ IsFinite gs ∧ Etale gs ∧ IsFinite gt ∧ Etale gt ∧ IsPIsog c o₀ o₀' ψ₀ ∧ IsTj r w j o₀ o₀' ψ₀ ∧ ∀ (S : Scheme.{0}) (x : S ⟶ M.X) (o₁ o₁' : Obj b N (x ≫ M.s)) (m₁ : ObjMap o₁ M.univ x) (ψ₁ : o₁.A ⟶ o₁'.A), IsUnit ((p : ℕ) : Γ(S, ⊤)) → IsPIsog c o₁ o₁' ψ₁ → IsTj r w j o₁ o₁' ψ₁ → ∃! y : S ⟶ Y₀, y ≫ s₀ = x ∧ ∃ (m₀ : ObjMap o₁ o₀ y) (m₂ : ObjMap o₁' o₀' y), m₀.φ ≫ ψ₀.left = ψ₁.left ≫ m₂.φ := by
  obtain ⟨T, hsf, hse, -, htf, hte, hUP⟩ := GlobalTheory.T.exists_finiteEtale_Tj_correspondence_p_invertible p D (Rp p R) (bb b) N hN hNp isUnit_Rp r w j c hw hu hj hc hm (mdl M)
  let gs : T.Y ⟶ (Uo M).toScheme := T.s
  let gt : T.Y ⟶ (Uo M).toScheme := T.t
  have h₁ : (gs ≫ sU M) ≫ πp p R = (gs ≫ (Uo M).ι) ≫ M.s := by
    rw [Category.assoc, sU_fac, Category.assoc]
  let o₀ : Obj b N ((gs ≫ (Uo M).ι) ≫ M.s) := toR h₁ T.o
  let o₀' : Obj b N ((gs ≫ (Uo M).ι) ≫ M.s) := toR h₁ T.o'
  have hst : gs ≫ sU M = gt ≫ sU M := T.st
  let ms : ObjMap o₀ (uO M) gs := cp T.ms
  let mt : ObjMap o₀' (uO M) gt := cp T.mt
  refine ⟨T.Y, gs ≫ (Uo M).ι, gt ≫ (Uo M).ι, gs, gt, o₀, o₀', MapComp.comp ms (uM M), MapComp.comp mt (uM M),
    T.ψ, ?_, rfl, rfl, hsf, hse, htf, hte, T.isog, T.tj, ?_⟩
  · rw [Category.assoc, Category.assoc, ← sU_fac, ← Category.assoc, ← Category.assoc, hst]
  · intro S x o₁ o₁' m₁ ψ₁ hpS hisog htj
    obtain ⟨x', rfl⟩ := exists_lift x hpS
    have h₂ : (x' ≫ sU M) ≫ πp p R = (x' ≫ (Uo M).ι) ≫ M.s := by
      rw [Category.assoc, sU_fac, Category.assoc]
    obtain ⟨m'⟩ := MapComp.cancel m₁ (uM M)
    let a₁ : Obj (bb (p := p) b) N (x' ≫ sU M) := ofR h₂ o₁
    let a₁' : Obj (bb (p := p) b) N (x' ≫ sU M) := ofR h₂ o₁'
    let m'' : ObjMap a₁ (mdl M).univ x' := cp m'
    obtain ⟨y, ⟨hy, m₀, m₂, e⟩, huq⟩ := hUP S x' a₁ a₁' m'' ψ₁ hpS hisog htj
    have hy' : y ≫ gs = x' := hy
    refine ⟨y, ⟨by rw [← Category.assoc, hy'], ⟨cp m₀, cp m₂, e⟩⟩, ?_⟩
    rintro y' ⟨hy₁, m₀', m₂', e'⟩
    have hy₂ : y' ≫ gs = x' := (cancel_mono (Uo M).ι).1 (by rw [Category.assoc]; exact hy₁)
    let n₀ : ObjMap a₁ T.o y' := cp m₀'
    let n₂ : ObjMap a₁' T.o' y' := cp m₂'
    exact huq y' ⟨hy₂, n₀, n₂, e'⟩

end UpperTheory.Cb.isogenyLiftUniqueness

open UpperTheory.Cb.isogenyLiftUniqueness in
theorem UpperTheory.Cb.exists_heckeCorrespondence_on_integral_shimuraModel :
    ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [CharZero R] (b : Base D R) (N : ℕ), 3 ≤ N → N.Coprime p → (p : R) ∈ IsLocalRing.maximalIdeal R → ∀ (r : ℤ) (w : Ideal (𝓞 D.F)) (j c : ℕ), w.IsMaximal → uIdeal D r ≤ w → j ≤ D.n → (∃ e : ℕ, c = p ^ e ∧ (0 < j → 0 < e)) → D.m = 1 → ∀ M : Model b N, ∃ (Y₀ : Scheme.{0}) (s₀ t₀ : Y₀ ⟶ M.X) (gs gt : Y₀ ⟶ (M.X.basicOpen ((p : ℕ) : Γ(M.X, ⊤))).toScheme) (o₀ o₀' : Obj b N (s₀ ≫ M.s)) (ms₀ : ObjMap o₀ M.univ s₀) (mt₀ : ObjMap o₀' M.univ t₀) (ψ₀ : o₀.A ⟶ o₀'.A), s₀ ≫ M.s = t₀ ≫ M.s ∧ gs ≫ (M.X.basicOpen ((p : ℕ) : Γ(M.X, ⊤))).ι = s₀ ∧ gt ≫ (M.X.basicOpen ((p : ℕ) : Γ(M.X, ⊤))).ι = t₀ ∧ IsFinite gs ∧ Etale gs ∧ IsFinite gt ∧ Etale gt ∧ IsPIsog c o₀ o₀' ψ₀ ∧ IsTj r w j o₀ o₀' ψ₀ ∧ ∀ (S : Scheme.{0}) (x : S ⟶ M.X) (o₁ o₁' : Obj b N (x ≫ M.s)) (m₁ : ObjMap o₁ M.univ x) (ψ₁ : o₁.A ⟶ o₁'.A), IsUnit ((p : ℕ) : Γ(S, ⊤)) → IsPIsog c o₁ o₁' ψ₁ → IsTj r w j o₁ o₁' ψ₁ → ∃! y : S ⟶ Y₀, y ≫ s₀ = x ∧ ∃ (m₀ : ObjMap o₁ o₀ y) (m₂ : ObjMap o₁' o₀' y), m₀.φ ≫ ψ₀.left = ψ₁.left ≫ m₂.φ := by
  intro p _ D R _ _ _ _ b N hN hNp _ r w j c hw hu hj hc hm M
  exact UpperTheory.Cb.isogenyLiftUniqueness.main hN hNp hw hu hj hc hm M

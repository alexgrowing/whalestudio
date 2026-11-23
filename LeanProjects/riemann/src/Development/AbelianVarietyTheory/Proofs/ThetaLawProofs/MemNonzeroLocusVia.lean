import Mathlib
import Development.AbelianVarietyTheory.Definitions.KeyFormula.IsSquareDeterminantComparison
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.IsPluriharmonicSiegel
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaUnifAV
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.MapsAtLeA
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.SymplecticCharacters.OneEqSpTranslZero
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyKa

noncomputable section
namespace GlobalTheory.KeyKa.EtBaseChange

section Val
variable {T T' : Type} [CommRing T] [CommRing T'] {X Y : Scheme.{0}}

def valH (w : Sp T ⟶ X) (U : X.Opens) (h : ⊤ ≤ w ⁻¹ᵁ U) : Γ(X, U) →+* T :=
  (w.appLE U ⊤ h ≫ (Scheme.ΓSpecIso (CommRingCat.of T)).hom).hom

theorem valT_eq (w : Sp T ⟶ X) (U : X.Opens) (h : ⊤ ≤ w ⁻¹ᵁ U) (a : Γ(X, U)) : valT w U a = valH w U h a :=
  dif_pos h

theorem valT_res (w : Sp T ⟶ X) {U V : X.Opens} (hle : V ≤ U) (h : ⊤ ≤ w ⁻¹ᵁ V) (a : Γ(X, U)) :
    valT w V (resG X hle a) = valT w U a := by
  have h' : ⊤ ≤ w ⁻¹ᵁ U := fun p hp => hle (h hp)
  rw [valT_eq w V h, valT_eq w U h']
  have e := congrArg (fun q => q.hom a) (w.map_appLE h (homOfLE hle).op)
  exact congrArg (Scheme.ΓSpecIso (CommRingCat.of T)).hom.hom e

theorem valT_appLE (w : Sp T ⟶ Y) (φ : Y ⟶ X) {U : X.Opens} {V : Y.Opens} (hle : V ≤ φ ⁻¹ᵁ U) (h : ⊤ ≤ w ⁻¹ᵁ V)
    (a : Γ(X, U)) : valT w V ((φ.appLE U V hle).hom a) = valT (w ≫ φ) U a := by
  have h' : ⊤ ≤ (w ≫ φ) ⁻¹ᵁ U := fun p hp => hle (h hp)
  rw [valT_eq w V h, valT_eq _ U h']
  have e := congrArg (fun q => q.hom a) (Scheme.Hom.appLE_comp_appLE w φ U V ⊤ hle h)
  exact congrArg (Scheme.ΓSpecIso (CommRingCat.of T)).hom.hom e

theorem valT_spMap (F : T →+* T') (w : Sp T ⟶ X) {U : X.Opens} (h : ⊤ ≤ w ⁻¹ᵁ U) (a : Γ(X, U)) :
    valT (spMap F ≫ w) U a = F (valT w U a) := by
  have h' : ⊤ ≤ (spMap F ≫ w) ⁻¹ᵁ U := fun p _ => h (show spMap F p ∈ ⊤ from trivial)
  rw [valT_eq w U h, valT_eq _ U h']
  have e := congrArg (fun q => q.hom a) (Scheme.Hom.appLE_comp_appLE (spMap F) w U ⊤ ⊤ h (fun _ _ => trivial))
  have e2 := congrArg (fun q => q.hom ((w.appLE U ⊤ h).hom a)) (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom F))
  refine (congrArg (Scheme.ΓSpecIso (CommRingCat.of T')).hom.hom e).symm.trans (Eq.trans ?_ e2)
  have e3 : (spMap F).appLE ⊤ ⊤ (fun _ _ => trivial) = (spMap F).appTop := Scheme.Hom.appLE_eq_app _
  simp only [e3]
  rfl

theorem fst_surjective (R : Type) [CommRing R] :
    Function.Surjective (spMap (TrivSqZeroExt.fstHom R R R).toRingHom) := by
  intro p
  have hs : Function.Surjective (TrivSqZeroExt.fstHom R R R).toRingHom := fun r => ⟨TrivSqZeroExt.inl r, rfl⟩
  have h : p ∈ PrimeSpectrum.zeroLocus (RingHom.ker (TrivSqZeroExt.fstHom R R R).toRingHom : Set (DualNumber R)) := by
    intro a ha
    have ha' : a.fst = 0 := ha
    refine (PrimeSpectrum.isPrime p).mem_of_pow_mem 2 ?_
    have : a ^ 2 = 0 := by
      ext <;> simp [sq, ha']
    rw [this]; exact Ideal.zero_mem _
  rw [← range_comap_of_surjective _ _ hs] at h
  exact h

theorem snd_map {R R' : Type} [CommRing R] [CommRing R'] (f : R →+* R') (F : DualNumber R →+* DualNumber R')
    (h₁ : ∀ a, F (algebraMap R _ a) = algebraMap R' _ (f a)) (h₂ : F DualNumber.eps = DualNumber.eps)
    (a : DualNumber R) : (F a).snd = f a.snd := by
  have : a = algebraMap R _ a.fst + algebraMap R _ a.snd * DualNumber.eps := by
    ext <;> simp [TrivSqZeroExt.algebraMap_eq_inl]
  conv_lhs => rw [this, map_add, map_mul, h₁, h₁, h₂]
  simp [TrivSqZeroExt.algebraMap_eq_inl]

theorem snd_pow_mul {R : Type} [CommRing R] (a b : DualNumber R) (n : ℕ) (hb : b.fst = 0) :
    (a ^ n * b).snd = a.fst ^ n * b.snd := by
  simp [hb]

end Val

section Dual
variable {R : Type} [CommRing R] {G : Over (Sp R)} [GrpObj G]

theorem fst_comp_translate (z : 𝟙_ (Over (Sp R)) ⟶ G) (v : epsR R ⟶ G) (hv : IsTangent v) :
    spMap (TrivSqZeroExt.fstHom R R R).toRingHom ≫ ((toUnit (epsR R) ≫ z) * v).left = z.left := by
  let r : 𝟙_ (Over (Sp R)) ⟶ epsR R := Over.homMk (spMap (TrivSqZeroExt.fstHom R R R).toRingHom) (by
    show spMap _ ≫ spMap _ = 𝟙 _
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ← Spec.map_id]
    congr 1)
  have h1 : r ≫ v = 1 := by
    have e₁ : (1 : 𝟙_ (Over (Sp R)) ⟶ G) = η[G] := by rw [Hom.one_def]; simp
    rw [e₁]
    exact Over.OverMorphism.ext hv
  have h2 : r ≫ toUnit (epsR R) ≫ z = z := by
    rw [← Category.assoc, toUnit_unique (r ≫ toUnit (epsR R)) (𝟙 _), Category.id_comp]
  have h3 : r ≫ ((toUnit (epsR R) ≫ z) * v) = z := by
    rw [MonObj.comp_mul, h1, h2, _root_.mul_one]
  exact congrArg CommaMorphism.left h3

theorem translate_le (z : 𝟙_ (Over (Sp R)) ⟶ G) (v : epsR R ⟶ G) (hv : IsTangent v) {U : G.left.Opens}
    (h : ⊤ ≤ z.left ⁻¹ᵁ U) : ⊤ ≤ ((toUnit (epsR R) ≫ z) * v).left ⁻¹ᵁ U := by
  intro p _
  obtain ⟨q, rfl⟩ := fst_surjective R p
  have := h (show q ∈ ⊤ from trivial)
  rw [← fst_comp_translate z v hv] at this
  exact this

theorem fst_valT_translate (z : 𝟙_ (Over (Sp R)) ⟶ G) (v : epsR R ⟶ G) (hv : IsTangent v) {U : G.left.Opens}
    (h : ⊤ ≤ z.left ⁻¹ᵁ U) (a : Γ(G.left, U)) :
    (valT (T := DualNumber R) ((toUnit (epsR R) ≫ z) * v).left U a).fst = valT (T := R) z.left U a := by
  have := valT_spMap (TrivSqZeroExt.fstHom R R R).toRingHom ((toUnit (epsR R) ≫ z) * v).left
    (translate_le z v hv h) a
  rw [fst_comp_translate z v hv] at this
  exact this.symm

theorem translate_comp {R' : Type} [CommRing R'] {G' : Over (Sp R')} [GrpObj G'] {f : R →+* R'}
    {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G (spMap f) φ) (F : DualNumber R →+* DualNumber R')
    (h₁ : ∀ a, F (algebraMap R _ a) = algebraMap R' _ (f a))
    (z : 𝟙_ (Over (Sp R)) ⟶ G) (z' : 𝟙_ (Over (Sp R')) ⟶ G') (hz : z'.left ≫ φ = spMap f ≫ z.left)
    (v : epsR R ⟶ G) (v' : epsR R' ⟶ G') (hv : v'.left ≫ φ = spMap F ≫ v.left) :
    ((toUnit (epsR R') ≫ z') * v').left ≫ φ = spMap F ≫ ((toUnit (epsR R) ≫ z) * v).left := by
  have hd : spMap F ≫ (epsR R).hom = (epsR R').hom ≫ spMap f := by
    have : F.comp (algebraMap R (DualNumber R)) = (algebraMap R' (DualNumber R')).comp f := RingHom.ext h₁
    show spMap _ ≫ spMap _ = spMap _ ≫ spMap _
    rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, this]
  let D : Over.mk ((epsR R').hom ≫ spMap f) ⟶ epsR R := Over.homMk (spMap F) hd
  have e : (D ≫ toUnit (epsR R) ≫ z).left = (toUnit (epsR R') ≫ z').left ≫ φ := by
    show spMap F ≫ (epsR R).hom ≫ z.left = ((epsR R').hom ≫ z'.left) ≫ φ
    exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ z.left) hd).trans ((Category.assoc _ _ _).trans
      ((congrArg ((epsR R').hom ≫ ·) hz.symm).trans (Category.assoc _ _ _).symm)))
  rw [← h.2 (epsR R') _ _ (D ≫ toUnit (epsR R) ≫ z) (D ≫ v) e hv.symm, ← MonObj.comp_mul]
  rfl

end Dual

section Via
variable {R R' : Type} [CommRing R] [CommRing R'] {x : KeyIn R} {x' : KeyIn R'} {φ : x'.P.A.left ⟶ x.P.A.left}
  {w : LB.Iso x'.P.L (x.P.L.pull φ)}

theorem le_inf_pull {T : Type} [CommRing T] (p : Sp T ⟶ x'.P.A.left) (c : x.P.L.ι) (c' : x'.P.L.ι)
    (h : ⊤ ≤ (p ≫ φ) ⁻¹ᵁ x.P.L.U c) (h' : ⊤ ≤ p ⁻¹ᵁ x'.P.L.U c') :
    ⊤ ≤ p ⁻¹ᵁ ((x.P.L.pull φ).U (fun _ => c) ⊓ x'.P.L.U c') :=
  fun _ hy => ⟨mem_pull.2 (h hy), h' hy⟩

theorem valT_via {T : Type} [CommRing T] {l : ℕ} {s' : RR x' l} {s : RR x l} (hs : SecVia x' x φ w s' s)
    (p : Sp T ⟶ x'.P.A.left) (c : x.P.L.ι) (c' : x'.P.L.ι)
    (h : ⊤ ≤ (p ≫ φ) ⁻¹ᵁ x.P.L.U c) (h' : ⊤ ≤ p ⁻¹ᵁ x'.P.L.U c') :
    valT (p ≫ φ) (x.P.L.U c) (s.f c) =
      valT p ((x.P.L.pull φ).U (fun _ => c) ⊓ x'.P.L.U c') (w.s (fun _ => c, c')).val ^ l *
        valT p (x'.P.L.U c') (s'.f c') := by
  have hle : (x.P.L.pull φ).U (fun _ => c) ⊓ x'.P.L.U c' ≤ φ ⁻¹ᵁ x.P.L.U c := fun y hy => mem_pull.1 hy.1
  have hp := le_inf_pull p c c' h h'
  have e := congrArg (valT p ((x.P.L.pull φ).U (fun _ => c) ⊓ x'.P.L.U c')) (hs (fun _ => c) c' hle)
  refine (valT_appLE p φ hle hp _).symm.trans (e.trans ?_)
  refine (valT_eq p _ hp _).trans ((map_mul _ _ _).trans (congrArg₂ (· * ·) ?_ ?_))
  · exact (map_pow _ _ _).trans (congrArg (· ^ l) (valT_eq p _ hp _).symm)
  · exact (valT_eq p _ hp _).symm.trans (valT_res p _ hp _)

theorem mem_nonzeroLocus_via {l : ℕ} {s' : RR x' l} {s : RR x l} (hs : SecVia x' x φ w s' s) (y : x'.P.A.left)
    (hy : φ y ∈ Out.nonzeroLocus s) : y ∈ Out.nonzeroLocus s' := by
  obtain ⟨k, hk⟩ := TopologicalSpace.Opens.mem_iSup.1 hy
  obtain ⟨i, hi⟩ := exists_chart x'.P.isLB y
  have hle : (x.P.L.pull φ).U (fun _ => k) ⊓ x'.P.L.U i ≤ φ ⁻¹ᵁ x.P.L.U k := fun y hy => mem_pull.1 hy.1
  have e := hs (fun _ => k) i hle
  have h1 : y ∈ x'.P.A.left.basicOpen ((φ.appLE _ _ hle).hom (s.f k)) := by
    have := Scheme.basicOpen_appLE φ _ (x.P.L.U k) hle (s.f k)
    refine this.ge ⟨⟨mem_pull.2 (x.P.A.left.basicOpen_le _ hk), hi⟩, hk⟩
  replace h1 := (Scheme.basicOpen_mul _ _ _).le ((congrArg x'.P.A.left.basicOpen e).le h1)
  refine TopologicalSpace.Opens.mem_iSup.2 ⟨i, ?_⟩
  exact ((Scheme.basicOpen_res _ _ _).le h1.2).2

end Via

end GlobalTheory.KeyKa.EtBaseChange

namespace GlobalTheory.KeyKa
open EtBaseChange

theorem etZ_baseChange : ∀ (R R' : Type) [CommRing R] [IsLocalRing R] [CommRing R'] [IsLocalRing R'] (x : KeyIn R) (x' : KeyIn R') (f : R →+* R') φ w (n d : ℕ) (hg : x'.P.g = x.P.g) (s : Fin x.P.g → RR x n) (s' : Fin x'.P.g → RR x' n) (z : Fin d → Pt x) (ch : Fin d → x.P.L.ι), KeyVia x' x f φ w → (∀ i, SecVia x' x φ w (s' i) (s (i.cast hg))) → EtZ x s z ch → ∃ (z' : Fin d → Pt x') (ch' : Fin d → x'.P.L.ι) (u : Fin d → R'ˣ), EtZ x' s' z' ch' ∧ (∀ a, jac x' s' (z' a) (ch' a) * (u a : R') ^ (x.P.g * n) = f (jac x s (z a) (ch a))) ∧ ∀ (l : ℕ) (sg : RR x l) (sg' : RR x' l) (a), SecVia x' x φ w sg' sg → valT (T := R') (z' a).left (x'.P.L.U (ch' a)) (sg'.f (ch' a)) * (u a : R') ^ l = f (valT (T := R) (z a).left (x.P.L.U (ch a)) (sg.f (ch a))) := by
  intro R R' _ _ _ _ x x' f φ w n d hg s s' z ch ⟨_, _, F, hp, _, _, _, hF₁, hF₂, hv⟩ hs ⟨hz₁, hz₂, hz₃, hz₄, hz₅⟩
  have hw : ∀ a, (spMap f ≫ (z a).left) ≫ x.P.A.hom = 𝟙 _ ≫ spMap f := fun a =>
    (Category.assoc _ _ _).trans ((congrArg (spMap f ≫ ·) (Over.w (z a))).trans
      ((Category.comp_id _).trans (Category.id_comp _).symm))
  let z' : Fin d → Pt x' := fun a => Over.homMk (hp.1.lift (spMap f ≫ (z a).left) (𝟙 _) (hw a)) (hp.1.lift_snd _ _ _)
  have hz' : ∀ a, (z' a).left ≫ φ = spMap f ≫ (z a).left := fun a => hp.1.lift_fst _ _ _
  have hch : ∀ a, ∃ i, ⊤ ≤ (z' a).left ⁻¹ᵁ x'.P.L.U i := fun a => by
    obtain ⟨i, hi⟩ := exists_chart x'.P.isLB ((z' a).left (IsLocalRing.closedPoint R'))
    exact ⟨i, fun p _ => ((IsLocalRing.specializes_closedPoint p).map (z' a).left.continuous).mem_open
      (x'.P.L.U i).isOpen hi⟩
  choose ch' hch' using hch
  have hφ : ∀ a, ⊤ ≤ ((z' a).left ≫ φ) ⁻¹ᵁ x.P.L.U (ch a) := fun a p _ => by
    rw [hz' a]
    exact hz₁ a (show spMap f p ∈ ⊤ from trivial)
  have hW := fun a => le_inf_pull (T := R') (z' a).left (ch a) (ch' a) (hφ a) (hch' a)
  let u : Fin d → R'ˣ := fun a => Units.map (valH (T := R') (z' a).left _ (hW a)).toMonoidHom (w.s (fun _ => ch a, ch' a))
  have hu : ∀ a, valT (T := R') (z' a).left ((x.P.L.pull φ).U (fun _ => ch a) ⊓ x'.P.L.U (ch' a))
      (w.s (fun _ => ch a, ch' a)).val = u a := fun a => valT_eq _ _ (hW a) _
  have hval : ∀ (l : ℕ) (sg : RR x l) (sg' : RR x' l) (a), SecVia x' x φ w sg' sg →
      valT (T := R') (z' a).left (x'.P.L.U (ch' a)) (sg'.f (ch' a)) * (u a : R') ^ l =
        f (valT (T := R) (z a).left (x.P.L.U (ch a)) (sg.f (ch a))) := fun l sg sg' a h => by
    have e := valT_via (T := R') h (z' a).left (ch a) (ch' a) (hφ a) (hch' a)
    rw [hu] at e
    refine (_root_.mul_comm _ _).trans (e.symm.trans ?_)
    exact (congrArg (fun q => valT (T := R') q (x.P.L.U (ch a)) (sg.f (ch a))) (hz' a)).trans
      (valT_spMap f (z a).left (hz₁ a) _)
  have hzero : ∀ a i, valT (T := R') (z' a).left (x'.P.L.U (ch' a)) ((s' i).f (ch' a)) = 0 := fun a i => by
    have e := hval n _ _ a (hs i)
    rw [hz₂, map_zero] at e
    exact ((u a).isUnit.pow n).mul_left_eq_zero.1 e
  have hjac : ∀ a, jac x' s' (z' a) (ch' a) * (u a : R') ^ (x.P.g * n) = f (jac x s (z a) (ch a)) := fun a => by
    have ent : ∀ i k, f (TrivSqZeroExt.snd (valT (T := DualNumber R) ((toUnit (epsR R) ≫ z a) * x.v (k.cast hg)).left
        (x.P.L.U (ch a)) ((s (i.cast hg)).f (ch a)))) = (u a : R') ^ n * TrivSqZeroExt.snd (valT (T := DualNumber R')
          ((toUnit (epsR R') ≫ z' a) * x'.v k).left (x'.P.L.U (ch' a)) ((s' i).f (ch' a))) := fun i k => by
      have c := translate_comp hp F hF₁ (z a) (z' a) (hz' a) (x.v (k.cast hg)) (x'.v k) (hv k)
      have l₁ := translate_le (z a) (x.v (k.cast hg)) (x.basis.1 _) (hz₁ a)
      have l₂ := translate_le (z' a) (x'.v k) (x'.basis.1 _) (hch' a)
      have l₃ : ⊤ ≤ (((toUnit (epsR R') ≫ z' a) * x'.v k).left ≫ φ) ⁻¹ᵁ x.P.L.U (ch a) := fun p _ => by
        rw [c]
        exact l₁ (show spMap F p ∈ ⊤ from trivial)
      have e := valT_via (T := DualNumber R') (hs i) _ (ch a) (ch' a) l₃ l₂
      have e₂ := (congrArg (fun q => valT (T := DualNumber R') q (x.P.L.U (ch a)) ((s (i.cast hg)).f (ch a))) c).trans
        (valT_spMap F _ l₁ _)
      refine (snd_map f F hF₁ hF₂ _).symm.trans ((congrArg TrivSqZeroExt.snd (e₂.symm.trans e)).trans ?_)
      refine (snd_pow_mul _ _ _ ((fst_valT_translate (z' a) (x'.v k) (x'.basis.1 _) (hch' a) _).trans (hzero a i))).trans ?_
      exact congrArg (· ^ n * _) ((fst_valT_translate (z' a) (x'.v k) (x'.basis.1 _) (hW a) _).trans (hu a))
    unfold jac
    rw [RingHom.map_det, ← Matrix.det_submatrix_equiv_self (finCongr hg), _root_.mul_comm, _root_.mul_comm x.P.g n,
      pow_mul]
    have hc : x.P.g = Fintype.card (Fin x'.P.g) := hg.symm.trans (Fintype.card_fin _).symm
    refine (congrArg (fun m => ((u a : R') ^ n) ^ m * _) hc).trans ((Matrix.det_smul _ _).symm.trans ?_)
    congr 1
    ext i k
    exact (ent i k).symm
  refine ⟨z', ch', u, ⟨hch', hzero, fun a => ?_, fun a a' h p e => ?_, fun y hy => ?_⟩, hjac, hval⟩
  · exact isUnit_of_mul_isUnit_left (hjac a ▸ (hz₃ a).map f)
  · refine hz₄ a a' h (spMap f p) ?_
    have e₁ := congrArg (fun q => q p) (hz' a)
    have e₂ := congrArg (fun q => q p) (hz' a')
    exact e₁.symm.trans ((congrArg φ e).trans e₂)
  · obtain ⟨a, p, hp'⟩ := hz₅ (φ y) fun i h => hy (i.cast hg.symm) (mem_nonzeroLocus_via (hs (i.cast hg.symm)) y h)
    have sq : IsPullback (spMap f) (z' a).left (z a).left φ := by
      refine IsPullback.of_bot (t := hp.1) ?_ (hz' a).symm
      have e₁ : (z' a).left ≫ x'.P.A.hom = 𝟙 _ := Over.w (z' a)
      have e₂ : (z a).left ≫ x.P.A.hom = 𝟙 _ := Over.w (z a)
      rw [e₁, e₂]
      exact IsPullback.of_vert_isIso (fst := spMap f) (snd := 𝟙 (Sp R')) (f := 𝟙 (Sp R)) (g := spMap f) ⟨by simp⟩
    obtain ⟨q, -, hq⟩ := Scheme.exists_preimage_of_isPullback sq p y hp'
    exact ⟨a, q, hq⟩

end GlobalTheory.KeyKa
end

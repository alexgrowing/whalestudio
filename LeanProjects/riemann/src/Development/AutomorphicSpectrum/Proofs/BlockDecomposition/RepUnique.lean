import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.LocDefs
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.GlobalSerreRelations.GlobSerreSt
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DFormMem
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FormAlternating
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FrameFormRespectsFiltration
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FrameFormCoboundaryRelation
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SheafFiltrationProperty
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ChartIsGood
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ChartDividedPowersGradedConstant
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsChartFromCoordinates
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris CrystallineSemistableComparison CrystallineSemistableComparison.Pb
open GlobalTheory.CatH (face toLast)

noncomputable section
namespace GlobalTheory.CompanionTheory.ConeLocal

section Rep
variable {R : Type} [CommRing R] {C : Type 1} [Category.{0} C] {A : C ⥤ CommAlgCat.{0} R}

theorem rep_add {a b : IdF A} {j : ℕ} {z z' : ∀ s : ComposableArrows C j, A.obj (s.obj (Fin.last j))}
    {c c' : CH.H (sq a b) j} (h : CrystallineSemistableComparison.Pb.Rep a b z c) (h' : CrystallineSemistableComparison.Pb.Rep a b z' c') :
    CrystallineSemistableComparison.Pb.Rep a b (fun s => z s + z' s) (c + c') := by
  obtain ⟨f, hf, rfl, hv⟩ := h
  obtain ⟨f', hf', rfl, hv'⟩ := h'
  refine ⟨f + f', by rw [map_add, hf, hf', add_zero], rfl, fun s => ?_⟩
  rw [map_add, ← hv, ← hv']
  rfl

theorem rep_smul {a b : IdF A} {j : ℕ} {z : ∀ s : ComposableArrows C j, A.obj (s.obj (Fin.last j))}
    {c : CH.H (sq a b) j} (r : R) (h : CrystallineSemistableComparison.Pb.Rep a b z c) :
    CrystallineSemistableComparison.Pb.Rep a b (fun s => r • z s) (r • c) := by
  obtain ⟨f, hf, rfl, hv⟩ := h
  refine ⟨r • f, by rw [map_smul, hf, smul_zero], rfl, fun s => ?_⟩
  have e : Ideal.Quotient.mk (b.S (s.obj (Fin.last j))) (r • z s) = r • Ideal.Quotient.mk (b.S (s.obj (Fin.last j))) (z s) := rfl
  rw [e, ← hv]
  rfl

theorem rep_congr {a b : IdF A} {j : ℕ} {z z' : ∀ s : ComposableArrows C j, A.obj (s.obj (Fin.last j))}
    {c : CH.H (sq a b) j} (h : CrystallineSemistableComparison.Pb.Rep a b z c) (e : ∀ s, z s - z' s ∈ b.S _) : CrystallineSemistableComparison.Pb.Rep a b z' c := by
  obtain ⟨f, hf, rfl, hv⟩ := h
  exact ⟨f, hf, rfl, fun s => (hv s).trans (Ideal.Quotient.eq.2 (e s))⟩

theorem rep_unique {a b : IdF A} {j : ℕ} {z : ∀ s : ComposableArrows C j, A.obj (s.obj (Fin.last j))}
    {c c' : CH.H (sq a b) j} (h : CrystallineSemistableComparison.Pb.Rep a b z c) (h' : CrystallineSemistableComparison.Pb.Rep a b z c') : c = c' := by
  obtain ⟨f, hf, rfl, hv⟩ := h
  obtain ⟨f', hf', rfl, hv'⟩ := h'
  have e : f = f' := funext fun s => Subtype.ext ((hv s).trans (hv' s).symm)
  subst e
  rfl

theorem rep_zero {a b : IdF A} {j : ℕ} {z : ∀ s : ComposableArrows C j, A.obj (s.obj (Fin.last j))}
    (e : ∀ s, z s ∈ b.S _) : CrystallineSemistableComparison.Pb.Rep a b z 0 := by
  refine ⟨0, map_zero _, ?_, fun s => ?_⟩
  · exact (Submodule.Quotient.mk_zero _).symm
  · exact (Ideal.Quotient.eq_zero_iff_mem.2 (e s)).symm

theorem d_val {a b : IdF A} {j : ℕ} (f : CH.Cn (sq a b) j) (z : ∀ s : ComposableArrows C j, A.obj (s.obj (Fin.last j)))
    (hv : ∀ s, (show sqM a b _ from f s).1 = Ideal.Quotient.mk _ (z s)) (s : ComposableArrows C (j + 1)) :
    (show sqM a b _ from CH.d _ j f s).1 = Ideal.Quotient.mk _
      (∑ i : Fin (j + 2), (-1 : ℤ) ^ (i : ℕ) • (A.map (toLast i s)).hom (z (face i s))) := by
  rw [map_sum]
  change Subtype.val (∑ i : Fin (j + 2), (-1 : ℤ) ^ (i : ℕ) • ((sq a b).map (toLast i s)).hom (f (face i s)) :
      sqM a b _) = _
  rw [AddSubmonoidClass.coe_finsetSum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_zsmul]
  change (-1 : ℤ) ^ (i : ℕ) • (sqMap a b (toLast i s) (f (face i s))).1 = _
  rw [GlobalTheory.CompanionTheory.GrDelta.sqMap_val a b _ _ _ (hv _)]

theorem rep_exists {a b : IdF A} {j : ℕ} (g : CH.Cn (CH.modF A) j) (hg : ∀ s, g s ∈ a.S _)
    (hd : ∀ s, CH.d _ j g s ∈ b.S _) : ∃ c, CrystallineSemistableComparison.Pb.Rep a b (fun s => g s) c := by
  let f : CH.Cn (sq a b) j := fun s => sqMk a b (g s) (hg s)
  have hd0 : CH.d _ j f = 0 := by
    funext s
    refine Subtype.ext ?_
    rw [d_val f (fun s => g s) (fun _ => rfl)]
    exact Ideal.Quotient.eq_zero_iff_mem.2 (hd s)
  exact ⟨_, f, hd0, rfl, fun _ => rfl⟩

theorem rep_d {a b : IdF A} {j : ℕ} (g : CH.Cn (CH.modF A) j) (hg : ∀ s, g s ∈ a.S _) :
    CrystallineSemistableComparison.Pb.Rep a b (fun s => CH.d _ j g s) 0 := by
  let f : CH.Cn (sq a b) j := fun s => sqMk a b (g s) (hg s)
  refine ⟨CH.d _ j f, CH.d_d _ j f, ?_, fun s => d_val f (fun s => g s) (fun _ => rfl) s⟩
  refine ((Submodule.Quotient.mk_eq_zero _).2 ?_).symm
  change CH.d _ j f ∈ (CH.cx _).B (j + 1)
  exact ⟨f, rfl⟩

end Rep

end GlobalTheory.CompanionTheory.ConeLocal

noncomputable section
namespace GlobalTheory.CompanionTheory.ConeLocal

section Res
variable {b : Base} {L : b.Fun}

theorem rep_res {Q Q' : ObjectProperty (Thick L)} (h : Q' ≤ Q) (r r' : ℤ) {j : ℕ}
    {z : ∀ s : ComposableArrows Q.FullSubcategory j, (sP Q).A.obj (s.obj (Fin.last j))} {x : HQ Q r r' j}
    (hx : CrystallineSemistableComparison.Pb.Rep (sFil Q r) (sFil Q r') z x) :
    CrystallineSemistableComparison.Pb.Rep (sFil Q' r) (sFil Q' r') (fun s => z (s ⋙ ObjectProperty.ιOfLE h))
      (((incl h).sq (incl_fil _ r) (incl_fil _ r')).pull j x) := by
  obtain ⟨f, hf, rfl, hv⟩ := hx
  refine ⟨((incl h).sq (incl_fil _ r) (incl_fil _ r')).pullC j f, ?_, rfl, fun s => ?_⟩
  · rw [CH.Mor.d_pullC, hf, map_zero]
  · change Ideal.quotientMap _ _ _ (show sqM _ _ _ from f (s ⋙ ObjectProperty.ιOfLE h)).1 = _
    rw [hv]
    rfl

def resQ {Q Q' : ObjectProperty (Thick L)} (h : Q' ≤ Q) {k : ℕ} (f : CH.Cn (CH.modF (sP Q).A) k) :
    CH.Cn (CH.modF (sP Q').A) k :=
  fun s => f (s ⋙ ObjectProperty.ιOfLE h)

theorem d_resQ {Q Q' : ObjectProperty (Thick L)} (h : Q' ≤ Q) {k : ℕ} (f : CH.Cn (CH.modF (sP Q).A) k) :
    CH.d _ k (resQ h f) = resQ h (CH.d _ k f) :=
  (CH.Mor.d_pullC (⟨ObjectProperty.ιOfLE h, fun _ => LinearMap.id, fun _ _ => rfl⟩ :
    CH.Mor (CH.modF (sP Q).A) (CH.modF (sP Q').A) (RingHom.id _)) k f)

theorem cup_resQ {Q Q' : ObjectProperty (Thick L)} (h : Q' ≤ Q) {k : ℕ} (ℓ : Fin k → CH.Cn (CH.modF (sP Q).A) 1) :
    resQ h (cupListC (sP Q).A ℓ) = cupListC (sP Q').A fun i => resQ h (ℓ i) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    funext s
    have e := ih fun i => ℓ (Fin.castSucc i)
    change _ = (CH.mulP (sP Q').A).cupC _ (cupListC (sP Q').A fun i => resQ h (ℓ (Fin.castSucc i))) (resQ h (ℓ (Fin.last k))) s
    rw [← e]
    rfl

end Res

section Frames
variable {R : Type} [CommRing R] {C : Type 1} [Category.{0} C] {Φ : PDF R C}

def Taylor (Fil : ℤ → IdF Φ.A) {d : ℕ} (E : Frame Φ d) (p : Fin d → Φ.A.obj E.D → Φ.A.obj E.D) : Prop :=
  ∀ (T : C) (u v : E.D ⟶ T) (x : Φ.A.obj E.D),
    (Φ.A.map u).hom x - (Φ.A.map v).hom x - ∑ k, E.τ k v u * (Φ.A.map v).hom (p k x) ∈ (Fil 2).S T

def sgn {m d : ℕ} (I : Idx m d) (J : Fin m → Fin d) : ℤ :=
  ∑ π : Equiv.Perm (Fin m), if J = I.1 ∘ π then (Equiv.Perm.sign π : ℤ) else 0

end Frames

section Loc
variable {K : Type} [CommRing K] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K))

def IsLoc (s : ℕ) {W : X.Opens} {d : ℕ} (t : Fin d → Γ(X, W)) (E : Frame (sP (KS q s {W})) d)
    (ε : Γ(X, W) ≃+* (sP (KS q s {W})).A.obj E.D) : Prop :=
  E.GrConst (sFil (KS q s {W})) ∧
  (∀ x, x ∈ (sFil (KS q s {W}) 1).S E.D → x = 0) ∧
  (∀ a : K, ε (strV q W a) = algebraMap K ((sP (KS q s {W})).A.obj E.D) a) ∧
  (∀ (T : (KS q s {W}).FullSubcategory) (u : E.D ⟶ T) (g : Γ(X, W)),
    ev T.obj (ks_in q s W _ T.property) g = Ideal.Quotient.mk T.obj.J (((sP (KS q s {W})).A.map u).hom (ε g))) ∧
  ∀ (i : Fin d) {T : (KS q s {W}).FullSubcategory} (u v : E.D ⟶ T),
    E.τ i u v = ((sP (KS q s {W})).A.map v).hom (ε (t i)) - ((sP (KS q s {W})).A.map u).hom (ε (t i))

end Loc
end GlobalTheory.CompanionTheory.ConeLocal

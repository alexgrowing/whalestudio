import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LocalisationLadders.CriterionTruncation
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.Coords
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.Imports
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiltrationCriticalComparisonMapStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TensTransfer
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EtaNat
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ClsCongr
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SqCSmul
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PullRestrictFirstPieceCompat
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb

set_option autoImplicit false
set_option linter.unusedVariables false

noncomputable section

namespace GlobalTheory.CompanionTheory.LocBC

section Initial

universe u v w

variable {R : Type} [CommRing R] {C : Type u} [Category.{v} C] (F : C ⥤ ModuleCat.{w} R) {D : C} (hD : Limits.IsInitial D)

def toH0 : F.obj D →ₗ[R] CH.H F 0 where
  toFun x := (CH.cx F).cls (CH.aug F (fun T => (F.map (hD.to T)).hom) x) ((CrystallineSemistableComparison.P.initial F D hD).1 x)
  map_add' x y := by
    have := (CrystallineSemistableComparison.P.cls_surj (CH.cx F) 0).2.2.2.1 _ _ ((CrystallineSemistableComparison.P.initial F D hD).1 x) ((CrystallineSemistableComparison.P.initial F D hD).1 y)
      (by rw [map_add, (CrystallineSemistableComparison.P.initial F D hD).1 x, (CrystallineSemistableComparison.P.initial F D hD).1 y, add_zero])
    exact (cls_congr (map_add _ x y) _ _).trans this
  map_smul' r x := by
    have := (CrystallineSemistableComparison.P.cls_surj (CH.cx F) 0).2.2.2.2 r _ ((CrystallineSemistableComparison.P.initial F D hD).1 x)
      (by rw [map_smul, (CrystallineSemistableComparison.P.initial F D hD).1 x, smul_zero])
    exact (cls_congr (map_smul _ r x) _ _).trans this

theorem toH0_bijective_of_initial : Function.Bijective (toH0 F hD) := by
  obtain ⟨h1, h2, h3, -⟩ := CrystallineSemistableComparison.P.initial F D hD
  constructor
  · rw [injective_iff_map_eq_zero]
    intro x hx
    have h := ((CrystallineSemistableComparison.P.cls_surj (CH.cx F) 0).2.1 _ (h1 x)).1 hx
    have h' := h2 x ((Submodule.mem_bot R).1 h)
    rwa [one_smul] at h'
  · intro c
    obtain ⟨f, hf, rfl⟩ := (CrystallineSemistableComparison.P.cls_surj (CH.cx F) 0).1 c
    obtain ⟨x, hx⟩ := h3 f hf
    rw [one_smul] at hx
    exact ⟨x, cls_congr hx _ _⟩

include hD in
theorem H_succ_sub (j : ℕ) : Subsingleton (CH.H F (j + 1)) := by
  obtain ⟨-, -, -, hex⟩ := CrystallineSemistableComparison.P.initial F D hD
  have key : ∀ x : CH.H F (j + 1), x = 0 := by
    intro x
    obtain ⟨a, ha, rfl⟩ := (CrystallineSemistableComparison.P.cls_surj (CH.cx F) (j + 1)).1 x
    refine ((CrystallineSemistableComparison.P.cls_surj (CH.cx F) (j + 1)).2.1 a ha).2 ?_
    obtain ⟨y, hy⟩ := hex j a ha
    rw [one_smul] at hy
    exact ⟨y, hy⟩
  exact ⟨fun x y => by rw [key x, key y]⟩

end Initial

variable {R R' : Type} [CommRing R] [CommRing R'] {ι : Type} [Fintype ι] [DecidableEq ι] {N : ι → Type}
  [∀ i, AddCommGroup (N i)] [∀ i, Module R (N i)]

section Base

variable {C C' : Type 1} [Category.{0} C] [Category.{0} C'] {Φ : PDF R C} {Φ' : PDF R' C'} {σ : R →+* R'} (m : SMor Φ Φ' σ)

theorem base_case {D : C} {D' : C'} (hD : Limits.IsInitial D) (hD' : Limits.IsInitial D') (e : D ⟶ m.G.obj D')
    (ν : ∀ i, N i → R') (a b : ι → IdF Φ.A) (a' b' : IdF Φ'.A) (ha : ∀ i n, m.LeC (ν i n) (a i) a')
    (hb : ∀ i n, m.LeC (ν i n) (b i) b')
    (h : Tens R (N := N) (M := fun i => (sq (a i) (b i)).obj D) (M' := (sq a' b').obj D')
      fun i n x => (m.sqC (ν i n) (ha i n) (hb i n)).τ D' (((sq (a i) (b i)).map e).hom x)) (j : ℕ) :
    Tens R (N := N) (M := fun i => CH.H (sq (a i) (b i)) j) (M' := CH.H (sq a' b') j)
      fun i n x => (m.sqC (ν i n) (ha i n) (hb i n)).pull j x := by
  cases j with
  | zero =>
    refine tens_transfer (fun i => LinearEquiv.ofBijective (toH0 (sq (a i) (b i)) hD) (toH0_bijective_of_initial _ hD))
      (LinearEquiv.ofBijective (toH0 (sq a' b') hD') (toH0_bijective_of_initial _ hD')).toAddEquiv _ _ (fun i n x => ?_) h
    change (m.sqC (ν i n) (ha i n) (hb i n)).hom.mapH 0 (toH0 (sq (a i) (b i)) hD x) = toH0 (sq a' b') hD' _
    have h1 := (CrystallineSemistableComparison.P.initial (sq (a i) (b i)) D hD).1 x
    refine (CrystallineSemistableComparison.P.mapH_cls _ 0 _ h1 (CrystallineSemistableComparison.CechClassBoundaries.cyc _ _ h1)).trans (cls_congr (funext fun s => ?_) _ _)
    change (m.sqC (ν i n) (ha i n) (hb i n)).τ _ (((sq (a i) (b i)).map (hD.to (m.G.obj (s.obj (Fin.last 0))))).hom x) =
      ((sq a' b').map (hD'.to (s.obj (Fin.last 0)))).hom ((m.sqC (ν i n) (ha i n) (hb i n)).τ D' (((sq (a i) (b i)).map e).hom x))
    rw [← (m.sqC (ν i n) (ha i n) (hb i n)).nat]
    congr 1
    have h2 := congrArg (fun t => ((sq (a i) (b i)).map t).hom x)
      (hD.hom_ext (hD.to (m.G.obj (s.obj (Fin.last 0)))) (e ≫ m.G.map (hD'.to (s.obj (Fin.last 0)))))
    simp only [Functor.map_comp, ModuleCat.hom_comp, LinearMap.comp_apply] at h2
    exact h2
  | succ j => exact tens_zero (fun i => H_succ_sub _ hD j) (H_succ_sub _ hD' j) _

end Base

section Step

variable [Algebra R R'] [∀ i, Module.Flat R (N i)] {C C' : Type 1} [Category.{0} C] [Category.{0} C']
  {Φ : PDF R C} {Φ' : PDF R' C'} (m : SMor Φ Φ' (algebraMap R R')) (Q : Poly Φ) (Q' : Poly Φ')
  {d : ℕ} (E : Frame Φ (d + 1)) (E' : Frame Φ' (d + 1)) (e : E.D ⟶ m.G.obj E'.D) (he : m.Fr E E' e)
  (hρ : ∀ T, Function.Injective (m.ρ T)) (ν : ∀ i, N i →ₗ[R] R')

theorem step (a b : ι → ℤ → IdF Φ.A) (a' b' : ℤ → IdF Φ'.A) (r : ℤ) (hQ : ∀ i, Q.Ladder (a i) (b i) r)
    (hQ' : Q'.Ladder a' b' r) (ha : ∀ i n r', m.LeC (ν i n) (a i r') (a' r')) (hb : ∀ i n r', m.LeC (ν i n) (b i r') (b' r'))
    (c1 : ∀ r₀, (r₀ = r ∨ r₀ = r - 1) → ∀ j, Tens R (N := N) (M := fun i => CH.H (sq ((a i r₀).res (Cut.U E)) ((b i r₀).res (Cut.U E))) j)
      (M' := CH.H (sq ((a' r₀).res (Cut.U E')) ((b' r₀).res (Cut.U E'))) j)
      fun i n x => ((m1 m E E' e he hρ).sqC (ν i n) (le_cover_restrict_compat m E E' e he hρ (ha i n r₀)) (le_cover_restrict_compat m E E' e he hρ (hb i n r₀))).pull j x)
    (j : ℕ) :
    Tens R (N := N) (M := fun i => CH.H (sq (a i r) (b i r)) j) (M' := CH.H (sq (a' r) (b' r)) j)
      fun i n x => (m.sqC (ν i n) (ha i n r) (hb i n r)).pull j x := by
  have hle : r - 1 ≤ r := by omega
  choose β hinj hex hsurj hform using fun i => GlobalTheory.T.filtration_critical_comparison_map Q E (a i) (b i) r (hQ i).le ((hQ i).ca r le_rfl)
    ((hQ i).ca _ hle) ((hQ i).cb r le_rfl) ((hQ i).cb _ hle)
  obtain ⟨β', hinj', hex', hsurj', hform'⟩ := GlobalTheory.T.filtration_critical_comparison_map Q' E' a' b' r hQ'.le (hQ'.ca r le_rfl)
    (hQ'.ca _ hle) (hQ'.cb r le_rfl) (hQ'.cb _ hle)
  have sI := fun i => CrystallineSemistableComparison.P.ses_cochains (alpha Q (a i r) (b i r)) (β i) (hinj i) (hex i) (hsurj i)
  have sP := CrystallineSemistableComparison.P.ses_cochains (alpha Q' (a' r) (b' r)) β' hinj' hex' hsurj'
  have hP : ∀ r₀, (r₀ = r ∨ r₀ = r - 1) → ∀ j, Tens R (N := N) (M := fun i => (CH.cx (Cut.P0 Q ⋙ Cut.U E ⋙ sq (a i r₀) (b i r₀))).H j)
      (M' := (CH.cx (Cut.P0 Q' ⋙ Cut.U E' ⋙ sq (a' r₀) (b' r₀))).H j)
      fun i n x => (mP m E E' e he hρ Q Q' (ν i n) (ha i n r₀) (hb i n r₀)).hom.mapH j x := by
    intro r₀ hr₀ j
    exact tens_transfer
      (fun i => LinearEquiv.ofBijective ((CH.Mor.restrict (sq ((a i r₀).res (Cut.U E)) ((b i r₀).res (Cut.U E))) (Cut.P0 Q)).pull j)
        (CrystallineSemistableComparison.P.adj _ (Cut.P0 Q) (Cut.inc E) (Cut.adj Q) j))
      ((LinearEquiv.ofBijective ((CH.Mor.restrict (sq ((a' r₀).res (Cut.U E')) ((b' r₀).res (Cut.U E'))) (Cut.P0 Q')).pull j)
        (CrystallineSemistableComparison.P.adj _ (Cut.P0 Q') (Cut.inc E') (Cut.adj Q') j)).toAddEquiv) _ _
      (fun i n x => pull_restrict_first_piece_compat m E E' e he hρ Q Q' (ν i n) (ha i n r₀) (hb i n r₀) j x) (c1 r₀ hr₀ j)
  have hPt := tens_les
    (K := fun i => CH.cx (Pt.U E ⋙ sq (a i r) (b i r)))
    (L := fun i => CH.cx (Cut.P0 Q ⋙ Cut.U E ⋙ sq (a i r) (b i r)))
    (M := fun i => CH.cx (Cut.P0 Q ⋙ Cut.U E ⋙ sq (a i (r - 1)) (b i (r - 1))))
    (K' := CH.cx (Pt.U E' ⋙ sq (a' r) (b' r)))
    (L' := CH.cx (Cut.P0 Q' ⋙ Cut.U E' ⋙ sq (a' r) (b' r)))
    (M' := CH.cx (Cut.P0 Q' ⋙ Cut.U E' ⋙ sq (a' (r - 1)) (b' (r - 1))))
    (fun i => (CH.Mor.ofNatTrans (alpha Q (a i r) (b i r))).hom) (fun i => (CH.Mor.ofNatTrans (β i)).hom)
    (fun i => (sI i).1) (fun i => (sI i).2.1) (fun i => (sI i).2.2)
    (CH.Mor.ofNatTrans (alpha Q' (a' r) (b' r))).hom (CH.Mor.ofNatTrans β').hom sP.1 sP.2.1 sP.2.2
    (fun i n => (mPt m E E' e (ν i n) (ha i n r) (hb i n r)).hom)
    (fun i n => (mP m E E' e he hρ Q Q' (ν i n) (ha i n r) (hb i n r)).hom)
    (fun i n => (mP m E E' e he hρ Q Q' (ν i n) (ha i n (r - 1)) (hb i n (r - 1))).hom)
    (fun i n k x => alpha_hom m E E' e he hρ Q Q' (ν i n) (ha i n r) (hb i n r) k x)
    (fun i n k x => funext fun s => beta_τ m E E' e he hρ Q Q' (ν i n) (ha i n) (hb i n) ((hQ i).ca r le_rfl)
      ((hQ i).ca _ hle) (β i) (hform i) β' hform' _ _)
    (hP r (Or.inl rfl)) (hP (r - 1) (Or.inr rfl))
    (fun i j => hadd_Pt m E E' e (ν i) (ha i · r) (hb i · r) j) j
  let u := fun i => LinearEquiv.ofBijective ((CH.Mor.restrict (sq (a i r) (b i r)) (Pt.U E)).pull j)
    (CrystallineSemistableComparison.P.adj _ (Pt.U E) (Pt.S E) (Pt.adj E) j)
  let u' := LinearEquiv.ofBijective ((CH.Mor.restrict (sq (a' r) (b' r)) (Pt.U E')).pull j)
    (CrystallineSemistableComparison.P.adj _ (Pt.U E') (Pt.S E') (Pt.adj E') j)
  refine tens_transfer (fun i => (u i).symm) u'.toAddEquiv.symm _ _ (fun i n x => ?_) hPt
  obtain ⟨z, rfl⟩ := (u i).surjective x
  rw [LinearEquiv.symm_apply_apply]
  symm
  refine (AddEquiv.symm_apply_eq u'.toAddEquiv).2 ?_
  exact pull_U m E E' e (ν i n) (ha i n r) (hb i n r) j z

end Step

section Main

variable [Algebra R R'] [∀ i, Module.Flat R (N i)]

theorem ladder_mono {C : Type 1} [Category.{0} C] {Φ : PDF R C} {Q : Poly Φ} {a b : ℤ → IdF Φ.A} {r r₀ : ℤ}
    (h : Q.Ladder a b r) (hr : r₀ ≤ r) : Q.Ladder a b r₀ :=
  ⟨h.le, fun r' hr' => h.ca r' (hr'.trans hr), fun r' hr' => h.cb r' (hr'.trans hr)⟩

theorem main (ν : ∀ i, N i →ₗ[R] R') : ∀ (d : ℕ) {C C' : Type 1} [Category.{0} C] [Category.{0} C']
    {Φ : PDF R C} {Φ' : PDF R' C'} (m : SMor Φ Φ' (algebraMap R R')) (Q : Poly Φ) (Q' : Poly Φ')
    (E : Frame Φ d) (E' : Frame Φ' d) (e : E.D ⟶ m.G.obj E'.D) (he : m.Fr E E' e)
    (hρ : ∀ T, Function.Injective (m.ρ T)) (a b : ι → ℤ → IdF Φ.A) (a' b' : ℤ → IdF Φ'.A) (r : ℤ)
    (hQ : ∀ i, Q.Ladder (a i) (b i) r) (hQ' : Q'.Ladder a' b' r)
    (ha : ∀ i n r', m.LeC (ν i n) (a i r') (a' r')) (hb : ∀ i n r', m.LeC (ν i n) (b i r') (b' r')),
    (∀ r', r - d ≤ r' → r' ≤ r → Tens R (N := N) (M := fun i => (sq (a i r') (b i r')).obj E.D) (M' := (sq (a' r') (b' r')).obj E'.D)
      fun i n x => (m.sqC (ν i n) (ha i n r') (hb i n r')).τ E'.D (((sq (a i r') (b i r')).map e).hom x)) →
    ∀ j, Tens R (N := N) (M := fun i => CH.H (sq (a i r) (b i r)) j) (M' := CH.H (sq (a' r) (b' r)) j)
      fun i n x => (m.sqC (ν i n) (ha i n r) (hb i n r)).pull j x := by
  intro d
  induction d with
  | zero =>
    intro C C' _ _ Φ Φ' m Q Q' E E' e he hρ a b a' b' r hQ hQ' ha hb h j
    exact base_case m (Frame.initial E) (Frame.initial E') e (fun i n => ν i n) (fun i => a i r) (fun i => b i r) (a' r) (b' r)
      (fun i n => ha i n r) (fun i n => hb i n r) (h r (by simp) le_rfl) j
  | succ d ih =>
    intro C C' _ _ Φ Φ' m Q Q' E E' e he hρ a b a' b' r hQ hQ' ha hb h j
    refine step m Q Q' E E' e he hρ ν a b a' b' r hQ hQ' ha hb (fun r₀ hr₀ j => ?_) j
    have hle : r₀ ≤ r := by rcases hr₀ with rfl | rfl <;> omega
    have hlo : r - 1 ≤ r₀ := by rcases hr₀ with rfl | rfl <;> omega
    exact ih (m1 m E E' e he hρ) (Cut.Q1 Q) (Cut.Q1 Q') (Cut.E1 E) (Cut.E1 E') (e1 m E E' e he hρ) (fr1 m E E' e he hρ)
      (fun T => hρ T.T) (fun i r => (a i r).res (Cut.U E)) (fun i r => (b i r).res (Cut.U E))
      (fun r => (a' r).res (Cut.U E')) (fun r => (b' r).res (Cut.U E')) r₀
      (fun i => Cut.ladder_truncation Q (ladder_mono (hQ i) hle)) (Cut.ladder_truncation Q' (ladder_mono hQ' hle))
      (fun i n r' => le_cover_restrict_compat m E E' e he hρ (ha i n r')) (fun i n r' => le_cover_restrict_compat m E E' e he hρ (hb i n r'))
      (fun r' h1 h2 => h r' (by push_cast; omega) (h2.trans hle)) j

end Main

theorem local_base_change : ∀ {R R' : Type} [CommRing R] [CommRing R'] [Algebra R R'] {C C' : Type 1} [Category.{0} C] [Category.{0} C']
    {Φ : PDF R C} {Φ' : PDF R' C'} (m : SMor Φ Φ' (algebraMap R R')) (Q : Poly Φ) (Q' : Poly Φ') {d : ℕ} (E : Frame Φ d)
    (E' : Frame Φ' d) (e : E.D ⟶ m.G.obj E'.D) (he : m.Fr E E' e) (hρ : ∀ T, Function.Injective (m.ρ T)) {ι : Type} [Fintype ι] [DecidableEq ι] (N : ι → Type)
    [∀ i, AddCommGroup (N i)] [∀ i, Module R (N i)] [∀ i, Module.Flat R (N i)] (ν : ∀ i, N i →ₗ[R] R')
    (a b : ι → ℤ → IdF Φ.A) (a' b' : ℤ → IdF Φ'.A) (r : ℤ) (hQ : ∀ i, Q.Ladder (a i) (b i) r) (hQ' : Q'.Ladder a' b' r)
    (ha : ∀ i n r', m.LeC (ν i n) (a i r') (a' r')) (hb : ∀ i n r', m.LeC (ν i n) (b i r') (b' r')),
    (∀ r', r - d ≤ r' → r' ≤ r → Tens R (N := N) (M := fun i => (sq (a i r') (b i r')).obj E.D) (M' := (sq (a' r') (b' r')).obj E'.D)
      fun i n x => (m.sqC (ν i n) (ha i n r') (hb i n r')).τ E'.D (((sq (a i r') (b i r')).map e).hom x)) →
    ∀ j, Tens R (N := N) (M := fun i => CH.H (sq (a i r) (b i r)) j) (M' := CH.H (sq (a' r) (b' r)) j)
      fun i n x => (m.sqC (ν i n) (ha i n r) (hb i n r)).pull j x := by
  intro R R' _ _ _ C C' _ _ Φ Φ' m Q Q' d E E' e he hρ ι _ _ N _ _ _ ν a b a' b' r hQ hQ' ha hb h j
  exact main ν d m Q Q' E E' e he hρ a b a' b' r hQ hQ' ha hb h j

end GlobalTheory.CompanionTheory.LocBC

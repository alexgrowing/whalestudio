import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.ConeSite
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.ZeroC
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.GlobalSerreRelations.GlobSerreSt
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RepUnique
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ChartRestrictPullBijective
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThickeningFiltrationIsFil
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RepresentativeRestrict
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsCupListRepresentative
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnitLogRepresentativeCompat
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FilteredCochainExtendOfSurjective
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TopRepresentativeAdd
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsUniqueTopGradedRep
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TopGradedRepRestrict
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TopGradedRepDerivationCompat
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TopGradedRepOpenCompat
set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris ReciprocityTheory.ChartRestriction.G.Geo.Tor CrystallineSemistableComparison CrystallineSemistableComparison.Pb

noncomputable section
namespace GlobalTheory.CompanionTheory.ConeTransfer

theorem pull_resU_comp {R : Type} [CommRing R] {C : Type 1} [Category.{0} C] (F : C ⥤ ModuleCat.{0} R)
    {U V W : ObjectProperty C} (h : V ≤ U) (h' : W ≤ V) (j : ℕ) (x : HU F U j) :
    (resU F h').pull j ((resU F h).pull j x) = (resU F (h'.trans h)).pull j x := by
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  rfl

section
variable {K : Type} [Field K] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K))

theorem resKS_eq (s : ℕ) {V V' : X.Opens} (h : V ≤ V') (r r' : ℤ) (j : ℕ) (x : HQ (KS q s {V'}) r r' j) :
    resKS q s h r r' j x =
      (resU (sq (thFil (smFun X q) r) (thFil (smFun X q) r')) (ks_le q s h)).pull j x := by
  unfold resKS
  rw [GlobalTheory.CompanionTheory.ConeZarCap.resU_eq]
  rfl

end

section
variable {K : Type} [Field K] [CharZero K] {X : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of K)}
  {Q : ObjectProperty (Thick (smFun X q))}

theorem isUnit_of_mk (T : Thick (smFun X q)) (x : T.B) (h : IsUnit (Ideal.Quotient.mk T.J x)) : IsUnit x :=
  (IsNilpotent.isUnit_quotient_mk_iff (GlobalTheory.CompanionTheory.ConeZcls.J_nil T)).1 h

theorem dlog_cocycle (s : ℕ) (hs : ∀ T : Q.FullSubcategory, T.obj.pdPow s = ⊥)
    (ĝ : ∀ T : Q.FullSubcategory, T.obj.B) (hu : ∀ T, IsUnit (ĝ T))
    (hc : ∀ (T T' : Q.FullSubcategory) (f : T ⟶ T'), ĝ T' - f.hom.φ (ĝ T) ∈ T'.obj.J) :
    CH.d _ 1 (dlogC Q s ĝ) = 0 := by
  choose v hv using hu
  obtain rfl : ĝ = fun T => (v T : T.obj.B) := funext fun T => (hv T).symm
  exact GlobalTheory.CompanionTheory.RepLifts.d_dlogC s hs v hc

theorem dlog_mem (s : ℕ) (ĝ : ∀ T : Q.FullSubcategory, T.obj.B) (hu : ∀ T, IsUnit (ĝ T))
    (hc : ∀ (T T' : Q.FullSubcategory) (f : T ⟶ T'), ĝ T' - f.hom.φ (ĝ T) ∈ T'.obj.J)
    (σ : ComposableArrows Q.FullSubcategory 1) : dlogC Q s ĝ σ ∈ (sFil Q 1).S _ := by
  have hF := GlobalTheory.CompanionTheory.DPFil.isFil_sFil Q
  choose v hv using hu
  obtain rfl : ĝ = fun T => (v T : T.obj.B) := funext fun T => (hv T).symm
  rw [hF.one]
  change (show (σ.obj (Fin.last 1)).obj.B from dlogC Q s (fun T => (v T : T.obj.B)) σ) ∈ (σ.obj (Fin.last 1)).obj.J
  rw [GlobalTheory.CompanionTheory.RepLifts.dlogC_eq s v σ]
  exact GlobalTheory.CompanionTheory.RepLifts.plogK_mem _ _ (GlobalTheory.CompanionTheory.RepLifts.rU_sub_mem v hc _)

end

theorem rep_uniqueU {R : Type} [CommRing R] {C : Type 1} [Category.{0} C] (A : C ⥤ CommAlgCat.{0} R) (a b : IdF A)
    (U : ObjectProperty C) {j : ℕ} (z : CH.Cn (CH.modF (U.ι ⋙ A)) j) (c c' : HU (sq a b) U j)
    (h : Rep (a.res U.ι) (b.res U.ι) z c) (h' : Rep (a.res U.ι) (b.res U.ι) z c') : c = c' := by
  obtain ⟨f, hf, hc, hz⟩ := h
  obtain ⟨f', hf', hc', hz'⟩ := h'
  have e : f = f' := funext fun s => Subtype.ext ((hz s).trans (hz' s).symm)
  subst e
  have a1 : c = (CH.cx (U.ι ⋙ sq a b)).cls f hf := hc
  have a2 : c' = (CH.cx (U.ι ⋙ sq a b)).cls f hf := hc'
  exact a1.trans a2.symm

theorem glue {R : Type} [CommRing R] {C : Type 1} [Category.{0} C] (F : C ⥤ ModuleCat.{0} R) {ι : Type} [Fintype ι]
    {Q P : ObjectProperty C} (A B : ι → ObjectProperty C) (h : P ≤ Q) (hA : ∀ j, Q ≤ A j) (hB : ∀ j, B j ≤ A j)
    (hP : ∀ j, P ≤ B j) (m : ℕ) (hi : Function.Injective ((resU F h).pull m))
    (c0 : HU F P m) (c x : HU F Q m) (ω' : ∀ j, HU F (A j) m) (ω : ∀ j, HU F (B j) m)
    (hω : ∀ j, (resU F (hB j)).pull m (ω' j) = ω j) (e0 : c0 = (resU F h).pull m c)
    (e2 : c0 - ∑ j, (resU F (hP j)).pull m (ω j) = (resU F h).pull m x) :
    c = ∑ j, (resU F (hA j)).pull m (ω' j) + x := by
  apply hi
  rw [map_add, map_sum, ← e0, ← e2]
  have e5 : ∀ j, (resU F h).pull m ((resU F (hA j)).pull m (ω' j)) = (resU F (hP j)).pull m (ω j) := fun j => by
    rw [← hω j, pull_resU_comp, pull_resU_comp]
  rw [Finset.sum_congr rfl fun j _ => e5 j]
  abel

theorem glue_res {R : Type} [CommRing R] {C : Type 1} [Category.{0} C] (F : C ⥤ ModuleCat.{0} R) {ι : Type} [Fintype ι]
    {Q W : ObjectProperty C} (A : ι → ObjectProperty C) (h : W ≤ Q) (hA : ∀ j, Q ≤ A j) (hW : ∀ j, W ≤ A j) (m : ℕ)
    (c x : HU F Q m) (ω' : ∀ j, HU F (A j) m) (e : c = ∑ j, (resU F (hA j)).pull m (ω' j) + x) :
    (resU F h).pull m c = ∑ j, (resU F (hW j)).pull m (ω' j) + (resU F h).pull m x := by
  rw [e, map_add, map_sum]
  refine congrArg (· + _) (Finset.sum_congr rfl fun j _ => ?_)
  rw [pull_resU_comp]

section
variable {K : Type} [Field K] {X : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of K)}

theorem rep_add' (s n : ℕ) (V : X.Opens) (t : Fin (n + 1) → Γ(X, V)) (x y : Γ(X, V))
    (a b : HQ (KS q s {V}) ((n : ℤ) + 1) ((n : ℤ) + 1 + 1) (n + 1))
    (ha : Rep (sFil (KS q s {V}) ((n : ℤ) + 1)) (sFil (KS q s {V}) ((n : ℤ) + 1 + 1)) (xdtC s V t x) a)
    (hb : Rep (sFil (KS q s {V}) ((n : ℤ) + 1)) (sFil (KS q s {V}) ((n : ℤ) + 1 + 1)) (xdtC s V t y) b) :
    Rep (sFil (KS q s {V}) ((n : ℤ) + 1)) (sFil (KS q s {V}) ((n : ℤ) + 1 + 1)) (xdtC s V t (x + y)) (a + b) :=
  GlobalTheory.CompanionTheory.ConeLocal.rep_xdtC_add (d := n + 1) s V t x y a b ha hb

theorem rep_sum (s n : ℕ) (V : X.Opens) (t : Fin (n + 1) → Γ(X, V))
    (h0 : Rep (sFil (KS q s {V}) ((n : ℤ) + 1)) (sFil (KS q s {V}) ((n : ℤ) + 1 + 1)) (xdtC s V t 0) 0)
    {ι : Type} [DecidableEq ι] (S : Finset ι) (x : ι → Γ(X, V))
    (a : ι → HQ (KS q s {V}) ((n : ℤ) + 1) ((n : ℤ) + 1 + 1) (n + 1))
    (h : ∀ j, Rep (sFil (KS q s {V}) ((n : ℤ) + 1)) (sFil (KS q s {V}) ((n : ℤ) + 1 + 1)) (xdtC s V t (x j)) (a j)) :
    Rep (sFil (KS q s {V}) ((n : ℤ) + 1)) (sFil (KS q s {V}) ((n : ℤ) + 1 + 1)) (xdtC s V t (∑ j ∈ S, x j)) (∑ j ∈ S, a j) := by
  induction S using Finset.induction_on with
  | empty => simpa using h0
  | insert j S hj ih =>
    rw [Finset.sum_insert hj, Finset.sum_insert hj]
    exact rep_add' s n V t _ _ _ _ (h j) ih

end

theorem rep_zero_xdt (h1 : CrystallineSemistableComparison.Pb.KH.LocGr) (h2 : CrystallineSemistableComparison.Pb.KH.PolyTf) (h3 : CrystallineSemistableComparison.Pb.KH.GrAff)
    {K : Type} [Field K] [CharZero K] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K)) (n : ℕ)
    [SmoothOfRelativeDimension (n + 1) q] (s : ℕ) (hs : n + 1 < s) (V : X.Opens) (c : Coord q V (n + 1)) :
    Rep (sFil (KS q s {V}) ((n : ℤ) + 1)) (sFil (KS q s {V}) ((n : ℤ) + 1 + 1)) (xdtC s V c.t 0) 0 := by
  obtain ⟨x, hx, hu⟩ := GlobalTheory.CompanionTheory.ConeTopChart.top_chart h1 h2 h3 q n s hs V c 0
  have h := rep_add' s n V c.t x x 0 0 hx hx
  rw [add_zero] at h
  have e : x + x = x := hu _ h
  have e0 : x = 0 := by simpa using e
  rwa [e0] at hx

set_option maxHeartbeats 1600000 in

theorem main : KH.LocGr → KH.PolyTf → KH.GrAff →
    ∀ {K : Type} [Field K] [CharZero K] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K)) (n : ℕ)
    [SmoothOfRelativeDimension (n + 1) q] {N : ℕ} (i : X ⟶ PSpace K N) (y : Fin (n + 2) → MvPolynomial (Fin (N + 1)) K),
    (∀ S : Finset (Fin (n + 2)), S.Nonempty → IsAffineOpen (⨅ k ∈ S, uy i y k)) →
    ∀ (V : X.Opens) (hV : ∀ S : Finset (Fin (n + 2)), V ≤ ⨅ k ∈ S, uy i y k) (c : Coord q V (n + 1)),
    letI := (strV q V).toAlgebra
    ∀ (D : Fin (n + 1) → Derivation K Γ(X, V) Γ(X, V)), (∀ k j, D k (c.t j) = if k = j then 1 else 0) →
    ∀ (g : Fin (n + 1) → Γ(X, ⨅ k ∈ Finset.univ, uy i y k)), (∀ k, IsUnit (g k)) →
    ∀ (ĝ : Fin (n + 1) → ∀ T : (capS (wK q i y (n + 2)) Finset.univ).FullSubcategory, T.obj.B),
    (∀ k T (h : InU (⨅ k ∈ Finset.univ, uy i y k) T.obj), Ideal.Quotient.mk _ (ĝ k T) = ev T.obj h (g k)) →
    ∀ (c0 : HU (gr (Φ := thP (smFun X q)) (thFil (smFun X q)) ((n : ℤ) + 1)) (capS (wK q i y (n + 2)) Finset.univ) (n + 1)),
    Rep ((thFil (smFun X q) ((n : ℤ) + 1)).res (capS (wK q i y (n + 2)) Finset.univ).ι)
      ((thFil (smFun X q) ((n : ℤ) + 1 + 1)).res (capS (wK q i y (n + 2)) Finset.univ).ι)
      (cupListC ((capS (wK q i y (n + 2)) Finset.univ).ι ⋙ thA (smFun X q)) fun k =>
        dlogC (capS (wK q i y (n + 2)) Finset.univ) (n + 2) (ĝ k)) c0 →
    ∀ (ω : ∀ j, HU (gr (Φ := thP (smFun X q)) (thFil (smFun X q)) ((n : ℤ) + 1))
        (capS (wK q i y (n + 2)) (Finset.univ.erase j)) (n + 1))
      (f : CH.Cn (CH.modF ((capS (wK q i y (n + 2)) Finset.univ).ι ⋙ thA (smFun X q))) n),
    (∀ σ, f σ ∈ (thFil (smFun X q) n).S _) → (∀ σ, CH.d _ n f σ ∈ (thFil (smFun X q) ((n : ℤ) + 1)).S _) →
    Rep ((thFil (smFun X q) ((n : ℤ) + 1)).res (capS (wK q i y (n + 2)) Finset.univ).ι)
      ((thFil (smFun X q) ((n : ℤ) + 1 + 1)).res (capS (wK q i y (n + 2)) Finset.univ).ι) (CH.d _ n f)
      (c0 - ∑ j, ((resU (gr (Φ := thP (smFun X q)) (thFil (smFun X q)) ((n : ℤ) + 1))
        (capS_univ_le (wK q i y (n + 2)) (Finset.univ.erase j))).pull (n + 1)) (ω j)) →
    ∃ (x : Fin (n + 2) → Γ(X, V)) (η : Fin (n + 1) → Γ(X, V)),
      (∀ j, x j ∈ jacSpan (hV (Finset.univ.erase j)) (RingHom.id _) (fun k => D k) id) ∧
      (∀ k, η k ∈ jacSpan (hV Finset.univ) (RingHom.id _) (fun k => D k) (Fin.succAbove k)) ∧
      (Ring.inverse (∏ k, rs (hV Finset.univ) (g k)) * (Matrix.of fun k l => D k (rs (hV Finset.univ) (g l))).det =
          ∑ j, x j + ∑ k : Fin (n + 1), (-1 : Γ(X, V)) ^ (k : ℕ) * D k (η k) ∨
        -(Ring.inverse (∏ k, rs (hV Finset.univ) (g k)) * (Matrix.of fun k l => D k (rs (hV Finset.univ) (g l))).det) =
          ∑ j, x j + ∑ k : Fin (n + 1), (-1 : Γ(X, V)) ^ (k : ℕ) * D k (η k)) := by
  intro hLG hPT hGA K _ _ X q n _ N i y haff V hV c D hD g hg ĝ hĝ c0 hc0 ω f hf hdf hrep
  have hun : (Finset.univ : Finset (Fin (n + 2))).Nonempty := Finset.univ_nonempty
  have her : ∀ j : Fin (n + 2), (Finset.univ.erase j).Nonempty := fun j => by
    refine ⟨if j = 0 then 1 else 0, ?_⟩
    simp only [Finset.mem_erase, Finset.mem_univ, and_true]
    split_ifs with h
    · subst h; exact (Fin.zero_ne_one).symm
    · exact fun e => h e.symm
  obtain ⟨h1, hb1⟩ := GlobalTheory.CompanionTheory.ConeZarCap.main q i y (n + 2) Finset.univ hun ((n : ℤ) + 1) ((n : ℤ) + 1 + 1) (n + 1)
  obtain ⟨h1', hb0⟩ := GlobalTheory.CompanionTheory.ConeZarCap.main q i y (n + 2) Finset.univ hun (n : ℤ) ((n : ℤ) + 1) n
  have hj := fun j : Fin (n + 2) => GlobalTheory.CompanionTheory.ConeZarCap.main q i y (n + 2) (Finset.univ.erase j) (her j) ((n : ℤ) + 1) ((n : ℤ) + 1 + 1) (n + 1)
  choose hjl hjb using hj
  have hle : ∀ j : Fin (n + 2), (⨅ k ∈ Finset.univ, uy i y k) ≤ (⨅ k ∈ Finset.univ.erase j, uy i y k) :=
    fun j => le_iInf₂ fun k _ => iInf₂_le k (Finset.mem_univ k)

  have hlift : ∀ k (T : (KS q (n + 2) {⨅ k ∈ Finset.univ, uy i y k}).FullSubcategory),
      Ideal.Quotient.mk T.obj.J (liftV T.obj (ks_in q (n + 2) _ T.obj T.property) (g k)) = ev T.obj (ks_in q (n + 2) _ T.obj T.property) (g k) :=
    fun k T => GlobalTheory.CompanionTheory.ConeLocal.XdtAdd.mk_liftV T.obj _ (g k)
  have hunit : ∀ k (T : (KS q (n + 2) {⨅ k ∈ Finset.univ, uy i y k}).FullSubcategory),
      IsUnit (liftV T.obj (ks_in q (n + 2) _ T.obj T.property) (g k)) := fun k T =>
    isUnit_of_mk T.obj _ ((hlift k T).symm ▸ (hg k).map (ev T.obj (ks_in q (n + 2) _ T.obj T.property)))
  have hcomp := fun k => GlobalTheory.CompanionTheory.RepLifts.lift_compat (Q := KS q (n + 2) {⨅ k ∈ Finset.univ, uy i y k})
    (ks_in q (n + 2) _) (g k) (fun T => liftV T.obj (ks_in q (n + 2) _ T.obj T.property) (g k)) (hlift k)
  obtain ⟨c', hc'⟩ : ∃ c' : HQ (KS q (n + 2) {(⨅ k ∈ Finset.univ, uy i y k)}) ((n : ℤ) + 1) ((n : ℤ) + 1 + 1) (n + 1), Rep (sFil (KS q (n + 2) {(⨅ k ∈ Finset.univ, uy i y k)}) ((n : ℤ) + 1)) (sFil (KS q (n + 2) {(⨅ k ∈ Finset.univ, uy i y k)}) ((n : ℤ) + 1 + 1))
      (cupListC (sP (KS q (n + 2) {(⨅ k ∈ Finset.univ, uy i y k)})).A fun k => dlogC _ (n + 2) fun T => liftV T.obj (ks_in q (n + 2) _ T.obj T.property) (g k)) c' := GlobalTheory.CompanionTheory.ConeRepCup.exists_rep (sP (KS q (n + 2) {⨅ k ∈ Finset.univ, uy i y k}))
    (sFil (KS q (n + 2) {⨅ k ∈ Finset.univ, uy i y k})) (GlobalTheory.CompanionTheory.DPFil.isFil_sFil _) (m := n + 1)
    (fun k => dlogC _ (n + 2) fun T => liftV T.obj (ks_in q (n + 2) _ T.obj T.property) (g k))
    (fun k => dlog_cocycle (n + 2) (fun T => T.property.1.1) _ (hunit k) (hcomp k))
    (fun k σ => dlog_mem (n + 2) _ (hunit k) (hcomp k) σ)
  have r1 := GlobalTheory.CompanionTheory.ConeRep.rep_resB (thA (smFun X q)) (thFil (smFun X q) ((n : ℤ) + 1)) (thFil (smFun X q) ((n : ℤ) + 1 + 1)) h1 _ c' hc'
  let ĝ2 : Fin (n + 1) → ∀ T : (capS (wK q i y (n + 2)) Finset.univ).FullSubcategory, T.obj.B :=
    fun k T => liftV T.obj (ks_in q (n + 2) _ T.obj (h1 _ T.property)) (g k)
  have e1 : resB (thA (smFun X q)) h1 (cupListC (sP (KS q (n + 2) {(⨅ k ∈ Finset.univ, uy i y k)})).A fun k => dlogC _ (n + 2) fun T => liftV T.obj (ks_in q (n + 2) _ T.obj T.property) (g k)) =
      cupListC (sP (capS (wK q i y (n + 2)) Finset.univ)).A fun k => dlogC (capS (wK q i y (n + 2)) Finset.univ) (n + 2) (ĝ2 k) :=
    GlobalTheory.CompanionTheory.ConeLocal.cup_resQ h1 _
  rw [e1] at r1
  have hρ : Rep (sFil (capS (wK q i y (n + 2)) Finset.univ) ((n : ℤ) + 1)) (sFil (capS (wK q i y (n + 2)) Finset.univ) ((n : ℤ) + 1 + 1)) (cupListC (sP (capS (wK q i y (n + 2)) Finset.univ)).A fun k => dlogC (capS (wK q i y (n + 2)) Finset.univ) (n + 2) (ĝ2 k)) c0 := GlobalTheory.CompanionTheory.RepLifts.main (capS (wK q i y (n + 2)) Finset.univ) (n + 2) (fun T hT => (h1 T hT).1.1) ĝ ĝ2
    (fun k T => isUnit_of_mk T.obj _ ((hĝ k T (ks_in q (n + 2) _ T.obj (h1 _ T.property))).symm ▸
      (hg k).map (ev T.obj (ks_in q (n + 2) _ T.obj (h1 _ T.property)))))
    (fun k => GlobalTheory.CompanionTheory.RepLifts.lift_compat (Q := (capS (wK q i y (n + 2)) Finset.univ)) (fun T hT => ks_in q (n + 2) _ T (h1 _ hT)) (g k) (ĝ k)
      (fun T => hĝ k T _))
    (fun k T => Ideal.Quotient.eq.1 ((hĝ k T (ks_in q (n + 2) _ T.obj (h1 _ T.property))).trans
      (GlobalTheory.CompanionTheory.ConeLocal.XdtAdd.mk_liftV T.obj _ (g k)).symm))
    c0 hc0
  have e0 : c0 = (resU (sq (thFil (smFun X q) ((n : ℤ) + 1)) (thFil (smFun X q) ((n : ℤ) + 1 + 1))) h1).pull (n + 1) c' := rep_uniqueU (thA (smFun X q)) (thFil (smFun X q) ((n : ℤ) + 1)) (thFil (smFun X q) ((n : ℤ) + 1 + 1)) (capS (wK q i y (n + 2)) Finset.univ) _ _ _ hρ r1

  have hω : ∀ j, ∃ w, (resU (sq (thFil (smFun X q) ((n : ℤ) + 1)) (thFil (smFun X q) ((n : ℤ) + 1 + 1))) (hjl j)).pull (n + 1) w = ω j := fun j => (hjb j).2 (ω j)
  choose ω' hω' using hω
  obtain ⟨f', hf'1, hf'2, hf'3⟩ := GlobalTheory.CompanionTheory.ConeRepExact.exact_lift (thP (smFun X q)) (thFil (smFun X q)) (GlobalTheory.CompanionTheory.DPFil.isFil_thFil _) h1 n hb0.2 f hf hdf
  obtain ⟨xf, hxf⟩ := GlobalTheory.CompanionTheory.ConeLocal.rep_exists (a := sFil (KS q (n + 2) {(⨅ k ∈ Finset.univ, uy i y k)}) ((n : ℤ) + 1)) (b := sFil (KS q (n + 2) {(⨅ k ∈ Finset.univ, uy i y k)}) ((n : ℤ) + 1 + 1))
    (CH.d _ n f') hf'2 (fun σ => by rw [CH.d_d]; exact zero_mem _)
  have e2 := hf'3 _ xf hrep hxf

  have t1 : Function.Injective ((resU (gr (Φ := thP (smFun X q)) (thFil (smFun X q)) ((n : ℤ) + 1)) h1).pull (n + 1)) := hb1.1
  have t2 : ∀ j, (resU (gr (Φ := thP (smFun X q)) (thFil (smFun X q)) ((n : ℤ) + 1)) (hjl j)).pull (n + 1) (ω' j) = ω j := hω'
  have t3 : c0 = (resU (gr (Φ := thP (smFun X q)) (thFil (smFun X q)) ((n : ℤ) + 1)) h1).pull (n + 1) c' := e0
  have t4 : c0 - ∑ j, (resU (gr (Φ := thP (smFun X q)) (thFil (smFun X q)) ((n : ℤ) + 1)) (capS_univ_le (wK q i y (n + 2)) (Finset.univ.erase j))).pull (n + 1) (ω j) = (resU (gr (Φ := thP (smFun X q)) (thFil (smFun X q)) ((n : ℤ) + 1)) h1).pull (n + 1) xf := e2
  have e3 := glue (gr (Φ := thP (smFun X q)) (thFil (smFun X q)) ((n : ℤ) + 1)) (fun j : Fin (n + 2) => KS q (n + 2) {⨅ k ∈ Finset.univ.erase j, uy i y k})
    (fun j : Fin (n + 2) => capS (wK q i y (n + 2)) (Finset.univ.erase j)) h1 (fun j => ks_le q (n + 2) (hle j)) hjl
    (fun j => capS_univ_le (wK q i y (n + 2)) (Finset.univ.erase j)) (n + 1) t1 c0 c' xf ω' ω t2 t3 t4

  have hUaff := haff _ hun
  have hd := GlobalTheory.CompanionTheory.ConeLdlog.main hLG hPT hGA q n (n + 2) (by omega) V _ (hV Finset.univ) hUaff c D hD g hg
    (fun k T => liftV T.obj (ks_in q (n + 2) _ T.obj T.property) (g k)) hlift c' hc'
  have hr := fun j : Fin (n + 2) => GlobalTheory.CompanionTheory.ConeLRestr.main hLG hPT hGA q n (n + 2) (by omega) V _ (hV (Finset.univ.erase j)) (haff _ (her j)) c D hD (ω' j)
  choose x hx hxr using hr
  obtain ⟨η, hη, hηr⟩ := GlobalTheory.CompanionTheory.ConeLocal.LExact.main hLG hPT hGA q n (n + 2) (by omega) V _ (hV Finset.univ) hUaff c D hD f' hf'1 hf'2 xf hxf
  have e4 : resKS q (n + 2) (hV Finset.univ) _ _ _ c' =
      ∑ j, resKS q (n + 2) (hV (Finset.univ.erase j)) _ _ _ (ω' j) + resKS q (n + 2) (hV Finset.univ) _ _ _ xf := by
    rw [resKS_eq, resKS_eq, Finset.sum_congr rfl fun j _ => resKS_eq q (n + 2) (hV (Finset.univ.erase j)) _ _ _ (ω' j)]
    exact glue_res (sq (thFil (smFun X q) ((n : ℤ) + 1)) (thFil (smFun X q) ((n : ℤ) + 1 + 1))) (fun j : Fin (n + 2) => KS q (n + 2) {⨅ k ∈ Finset.univ.erase j, uy i y k}) (ks_le q (n + 2) (hV Finset.univ))
      (fun j => ks_le q (n + 2) (hle j)) (fun j => ks_le q (n + 2) (hV (Finset.univ.erase j))) (n + 1) c' xf ω' e3
  have hsum := rep_add' (n + 2) n V c.t _ _ _ _
    (rep_sum (n + 2) n V c.t (rep_zero_xdt hLG hPT hGA q n (n + 2) (by omega) V c) Finset.univ x _ hxr) hηr
  rw [← e4] at hsum
  refine ⟨x, η, hx, hη, ?_⟩
  rcases hd with hd | hd
  · exact Or.inl ((GlobalTheory.CompanionTheory.ConeTopChart.top_chart hLG hPT hGA q n (n + 2) (by omega) V c _).unique hd hsum)
  · exact Or.inr ((GlobalTheory.CompanionTheory.ConeTopChart.top_chart hLG hPT hGA q n (n + 2) (by omega) V c _).unique hd hsum)

end GlobalTheory.CompanionTheory.ConeTransfer

import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.PhiIterPull
import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.TorsionOfVec
import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.SplitOnOfDisj
import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.SplitPointGeneric
import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.MapUSharp
import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.AveragingTransferKills
import Development.AutomorphicArithmetic.EtaleIdempotents.ExistsCrystallineLatticeExpansion
import Development.AutomorphicArithmetic.EtaleIdempotents.HeckeCorrespondenceProduct
import Development.AutomorphicArithmetic.EtaleIdempotents.LinearCombinationTransferOfProjectorRelations
import Development.AutomorphicArithmetic.EtaleIdempotents.CrystallineExpansionRelationOfScaledEndomorphism
import Development.AutomorphicArithmetic.EtaleIdempotents.NatCastPrimeNeZeroAndNotIsUnitIntegers

set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry GroundTheory.PAdicHodge CrystallineSemistableComparison TensorProduct

namespace UpperTheory.Ru.crystallineComparison

open UpperTheory.Gal.crystallineComparison

private theorem phiTL {l : ℕ} [Fact l.Prime] : phiA l (tA l) = (l : Acris l) * tA l := ACris.phi_periodT_eq_mul _

private lemma eqAbs {A : Type} [CommRing A] {H : Type 1} [AddCommGroup H] [Module A H] (Φ : H → H) (ph : A → A)
    (hs : ∀ c x, Φ (c • x) = ph c • Φ x) {c1 c2 c1' c2' : A} {E E' Y Y' : H} (hX : c1 • E = c2 • Y)
    (h1 : ph c1 = c1') (h2 : ph c2 = c2') (hE : Φ E = E') (hY : Φ Y = Y') : c1' • E' = c2' • Y' := by
  subst h1 h2 hE hY
  rw [← hs, ← hs, hX]

private lemma scaleAbs {A : Type} [CommRing A] {H : Type 1} [AddCommGroup H] [Module A H] (d : A) {c1 c2 c1' c2' : A} {E Y : H}
    (h1 : c1' = d * c1) (h2 : c2' = d * c2) (h : c1 • E = c2 • Y) : c1' • E = c2' • Y := by
  rw [h1, h2, mul_smul, mul_smul, h]

private lemma phi_iter_l {l : ℕ} [Fact l.Prime] (m : ℕ) : (phiA l)^[m] (l : Acris l) = (l : Acris l) := by
  induction m with
  | zero => rfl
  | succ m ih => rw [Function.iterate_succ_apply', ih, map_natCast]

private lemma phiA_iterate_tA_of_prime {l : ℕ} [Fact l.Prime] (m : ℕ) : (phiA l)^[m] (tA l) = (l : Acris l) ^ m * tA l := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Function.iterate_succ_apply', ih, map_mul, map_pow, map_natCast, phiTL]
    ring

private lemma phiH_iter_smul {l : ℕ} [Fact l.Prime] (P : PAlg l ⥤ Type) (n j m : ℕ) (c : Acris l) (x : MH P n j) :
    (phiH P n j)^[m] (c • x) = ((phiA l)^[m] c) • (phiH P n j)^[m] x := by
  induction m with
  | zero => rfl
  | succ m ih =>
    have h1 : (phiH P n j)^[m + 1] (c • x) = phiH P n j ((phiH P n j)^[m] (c • x)) := Function.iterate_succ_apply' _ _ _
    have h2 : (phiH P n j)^[m + 1] x = phiH P n j ((phiH P n j)^[m] x) := Function.iterate_succ_apply' _ _ _
    have h3 : (phiA l)^[m + 1] c = phiA l ((phiA l)^[m] c) := Function.iterate_succ_apply' _ _ _
    refine h1.trans ((congrArg (phiH P n j) ih).trans ?_)
    refine (((phiMor P n).pull j).map_smulₛₗ _ _).trans ?_
    exact (congrArg₂ (· • ·) h3 h2).symm

variable {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)}

private lemma phiH_evE {e : E.EtFam l K} (he : e.Good) (M : Model l K) (j lev : ℕ) {ι : Type} [Fintype ι] (v : ι → M.T j)
    (c : ι → Acris l) (m : ℕ) :
    (phiH M.P lev j)^[m] (evE e M j lev v c) = evE e M j lev v (fun k => (phiA l)^[m] (c k)) := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [Function.iterate_succ_apply', ih]
    simp only [evE, Function.iterate_succ_apply']
    refine (map_sum ((phiMor M.P lev).pull j) _ _).trans (Finset.sum_congr rfl fun k _ => ?_)
    refine (((phiMor M.P lev).pull j).map_smulₛₗ _ _).trans ?_
    exact congrArg (_ • ·) (he.phi M lev j _)

private lemma eqI {e : E.EtFam l K} (he : e.Good) (M : Model l K) (j lev : ℕ) {ι : Type} [Fintype ι] (v : ι → M.T j)
    (c c' : ι → Acris l) (Y : M.MH lev j) (a u r m d M0 : ℕ) (hM : m + d = M0)
    (hc : (fun k => (phiA l)^[m] (c k)) = c')
    (hX : ((l : Acris l) ^ a * tA l ^ u) • evE e M j lev v c = tA l ^ (u + r) • Y) :
    (((l : Acris l) ^ (a + M0 * u) * tA l ^ u) * (l : Acris l) ^ (d * r)) • evE e M j lev v c' =
      ((l : Acris l) ^ (M0 * (u + r)) * tA l ^ (u + r)) • (phiH M.P lev j)^[m] Y := by
  subst hM hc
  have c1 : (phiA l)^[m] ((l : Acris l) ^ a * tA l ^ u) = (l : Acris l) ^ a * ((l : Acris l) ^ m * tA l) ^ u := by
    rw [iterate_map_mul (phiA l), iterate_map_pow (phiA l), iterate_map_pow (phiA l), phi_iter_l, phiA_iterate_tA_of_prime]
  have c2 : (phiA l)^[m] (tA l ^ (u + r)) = ((l : Acris l) ^ m * tA l) ^ (u + r) := by
    rw [iterate_map_pow (phiA l), phiA_iterate_tA_of_prime]
  have q1 : ((l : Acris l) ^ (a + (m + d) * u) * tA l ^ u) * (l : Acris l) ^ (d * r) =
      (l : Acris l) ^ (d * (u + r)) * ((l : Acris l) ^ a * ((l : Acris l) ^ m * tA l) ^ u) := by ring
  have q2 : (l : Acris l) ^ ((m + d) * (u + r)) * tA l ^ (u + r) =
      (l : Acris l) ^ (d * (u + r)) * ((l : Acris l) ^ m * tA l) ^ (u + r) := by ring
  exact scaleAbs (H := MH M.P lev j) _ q1 q2
    (eqAbs (H := MH M.P lev j) _ _ (phiH_iter_smul M.P lev j m) hX c1 c2 (phiH_evE he M j lev v c m) rfl)

private def eLev (e : E.EtFam l K) (M : Model l K) (j lev : ℕ) : M.T j →+ M.MH lev j :=
  AddMonoidHom.mk' (fun x => e M lev j (x.lev lev)) fun x y => map_add (e M lev j) (x.lev lev) (y.lev lev)

private lemma natS {A : Type} [CommRing A] {H : Type 1} [AddCommGroup H] [Module A H] (n b : ℕ) (x : H) :
    (n ^ b : ℕ) • x = ((n : A) ^ b) • x := by
  rw [← Nat.cast_smul_eq_nsmul A]
  push_cast
  rfl

private lemma h1A {A : Type} [CommRing A] {TW H : Type 1} [AddCommGroup TW] [AddCommGroup H] [Module A H] (Ψ : TW →+ H)
    {d l s b : ℕ} (p : TW) (q : Fin d → TW) (p' : H) (q' : Fin d → H)
    (h : (l ^ b : ℕ) • p = (l ^ (s + b) : ℕ) • ∑ a, q a) (hp : Ψ p = p') (hq : ∀ a, Ψ (q a) = q' a) :
    ((l : A) ^ b) • p' = ((l : A) ^ (s + b)) • ∑ a, q' a := by
  have h' := congrArg Ψ h
  rw [map_nsmul, map_nsmul, map_sum, hp] at h'
  simp only [hq] at h'
  rw [natS (A := A), natS (A := A)] at h'
  exact h'

private lemma natE {e : E.EtFam l K} (he : e.Good) (W M : Model l K) (u : W.X ⟶ M.X) (hu : u ≫ M.p = W.p) (j lev : ℕ) (y : M.T j) :
    eLev e W j lev (Model.pullT u hu j y) = pullH (pxMap (okToOC l K) u hu) lev j (e M lev j (y.lev lev)) :=
  he.nat W M u hu lev j (y.lev lev)

private lemma h1L {e : E.EtFam l K} (he : e.Good) (W M : Model l K) (π : W.X ⟶ M.X) (hπ : π ≫ M.p = W.p) (j lev s b : ℕ)
    {d : ℕ} (τ : Fin d → (W.X ⟶ M.X)) (hτ : ∀ a, τ a ≫ M.p = W.p) (w y : M.T j)
    (h : (l ^ b : ℕ) • Model.pullT π hπ j w = (l ^ (s + b) : ℕ) • ∑ a, Model.pullT (τ a) (hτ a) j y) :
    ((l : Acris l) ^ b) • pullH (pxMap (okToOC l K) π hπ) lev j (e M lev j (w.lev lev)) =
      ((l : Acris l) ^ (s + b)) • ∑ a, pullH (pxMap (okToOC l K) (τ a) (hτ a)) lev j (e M lev j (y.lev lev)) := by
  exact h1A (A := Acris l) (H := MH W.P lev j) (eLev e W j lev) _ _ _ _ h (natE he W M π hπ j lev w)
    fun a => natE he W M (τ a) (hτ a) j lev y

private lemma finA {A : Type} [CommRing A] {H : Type 1} [AddCommGroup H] [Module A H] {Q : Type} [Fintype Q] (C : ℕ)
    (Ev : Q → H) (c : Q → A) (L tt κ : A) (hk : tt * κ = (C : A) * L)
    (h : C • (L • ∑ q, c q • Ev q) = 0) : tt • ∑ q, (κ * c q) • Ev q = 0 := by
  have e1 : ∑ q, (κ * c q) • Ev q = κ • ∑ q, c q • Ev q := by
    rw [Finset.smul_sum]
    exact Finset.sum_congr rfl fun q _ => mul_smul _ _ _
  rw [e1, smul_smul, hk, mul_smul, Nat.cast_smul_eq_nsmul]
  exact h

set_option maxHeartbeats 4000000 in
private lemma levZero {e : E.EtFam l K} (he : e.Good) (M W : Model l K) (π : W.X ⟶ M.X) (hπ : π ≫ M.p = W.p)
    (j n f N0 N1 r s b a u C : ℕ) {d : Fin (n + 1) → ℕ} (τ : ∀ i, Fin (d i) → (W.X ⟶ M.X)) (hτ : ∀ i x, τ i x ≫ M.p = W.p)
    {ι : Type} [Fintype ι] (v : ι → M.T j) (c : ι → Acris l) (w : Fin (n + 1) → ι → M.T j) (σ : Fin (n + 1) → ℤ)
    (Y : ∀ lev, MH M.P lev j)
    (hAvg : ∀ lev (x : MH M.P lev j), pullH (pxMap (okToOC l K) π hπ) lev j x = 0 → C • x = 0)
    (h3 : ∀ lev, ∑ x : Σ i, Fin (d i), σ x.1 • pullH (pxMap (okToOC l K) (τ x.1 x.2) (hτ x.1 x.2)) lev j
      ((phiH M.P lev j)^[f * (n - x.1 + N0)] (Y lev)) = 0)
    (hX : ∀ lev, ((l : Acris l) ^ a * tA l ^ u) • evE e M j lev v (fun k => (phiA l)^[f * N1] (c k)) = tA l ^ (u + r) • Y lev)
    (hw2 : ∀ i k, (l ^ b : ℕ) • Model.pullT π hπ j (w i k) = (l ^ (s + b) : ℕ) • ∑ x, Model.pullT (τ i x) (hτ i x) j (v k))
    (lev : ℕ) :
    tA l ^ u • evE e M j lev (fun q : Fin (n + 1) × ι => w q.1 q.2)
      (fun q => ((C * l ^ (a + f * (n + N0) * u) * l ^ b : ℕ) : Acris l) *
        (((σ q.1 : ℤ) : Acris l) * (l : Acris l) ^ (f * (q.1 : ℕ) * r) * (phiA l)^[f * (n - q.1 + (N0 + N1))] (c q.2))) = 0 := by
  have h2 : ∀ i : Fin (n + 1), (((l : Acris l) ^ (a + f * (n + N0) * u) * tA l ^ u) * (l : Acris l) ^ (f * (i : ℕ) * r)) •
      evE e M j lev v (fun k => (phiA l)^[f * (n - i + (N0 + N1))] (c k)) =
      ((l : Acris l) ^ (f * (n + N0) * (u + r)) * tA l ^ (u + r)) • (phiH M.P lev j)^[f * (n - i + N0)] (Y lev) := by
    intro i
    have hi : (i : ℕ) ≤ n := Nat.lt_succ_iff.1 i.2
    have hM : f * (n - i + N0) + f * i = f * (n + N0) := by
      rw [← mul_add]
      congr 1
      omega
    have hI : (fun k => (phiA l)^[f * (n - i + (N0 + N1))] (c k)) = fun k => (phiA l)^[f * (n - i + N0)] ((phiA l)^[f * N1] (c k)) := by
      funext k
      rw [← Function.iterate_add_apply]
      congr 1
      ring
    exact eqI he M j lev v (fun k => (phiA l)^[f * N1] (c k)) _ (Y lev) a u r (f * (n - i + N0)) (f * i) _ hM hI.symm (hX lev)
  have S := UpperTheory.linear_combination_transfer_of_projector_relations (A := Acris l) (H := MH M.P lev j) (H' := MH W.P lev j) (J := Fin (n + 1)) (ι := ι) (I := fun i => Fin (d i))
    (pullH (pxMap (okToOC l K) π hπ) lev j) (fun i x => pullH (pxMap (okToOC l K) (τ i x) (hτ i x)) lev j)
    (fun k => e M lev j ((v k).lev lev)) (fun i k => e M lev j ((w i k).lev lev))
    ((l : Acris l) ^ b) ((l : Acris l) ^ (s + b)) ((l : Acris l) ^ (a + f * (n + N0) * u) * tA l ^ u)
    ((l : Acris l) ^ (f * (n + N0) * (u + r)) * tA l ^ (u + r)) σ (fun i => (l : Acris l) ^ (f * (i : ℕ) * r))
    (fun i k => (phiA l)^[f * (n - i + (N0 + N1))] (c k)) (fun i => (phiH M.P lev j)^[f * (n - i + N0)] (Y lev))
    (fun i k => h1L he W M π hπ j lev s b (τ i) (hτ i) (w i k) (v k) (hw2 i k)) h2 (h3 lev)
  rw [← map_smul] at S
  have A1 := hAvg lev _ S
  refine finA (A := Acris l) (H := MH M.P lev j) C (fun q : Fin (n + 1) × ι => e M lev j ((w q.1 q.2).lev lev)) _
    (((l : Acris l) ^ (a + f * (n + N0) * u) * tA l ^ u) * (l : Acris l) ^ b) _ _ ?_ A1
  push_cast
  ring

end UpperTheory.Ru.crystallineComparison

open CategoryTheory Limits AlgebraicGeometry GroundTheory.PAdicHodge CrystallineSemistableComparison TensorProduct UpperTheory.Gal.crystallineComparison UpperTheory.Ru.crystallineComparison in
set_option maxHeartbeats 4000000 in
theorem UpperTheory.Ru.crystallineComparison.top : UpperTheory.Ru.crystallineComparison.Top := by
  intro l _ K _ _ ϖ hϖ e he M hsm hqc haff f n j hf T hr hPt A hA B hInj hAbs
  obtain ⟨m, N1, g, F, ρ, hg0, hgf, hF, hρ, hAI⟩ := hAbs
  obtain ⟨D⟩ := wEx l M.X (Fin (n + 1)) T
  obtain ⟨N0, hZ⟩ := wZero l f n (OK l K) ϖ hϖ UpperTheory.natCast_prime_ne_zero_and_not_isUnit_integers.1 UpperTheory.natCast_prime_ne_zero_and_not_isUnit_integers.2 M.X M.p hsm hqc haff hf T hr hPt (okToOC l K) g hg0 m F ρ hF hρ hgf D
  obtain ⟨gp, hgp⟩ := wTrans l (OK l K) M.X M.p (okToOC l K) (Fin (n + 1)) T D
  refine ⟨N0 + N1, fun x hx => ?_⟩
  obtain ⟨ι, _, v, c, r, rfl⟩ := UpperTheory.exists_crystalline_lattice_expansion B M j x
  obtain ⟨a, u, X, hX⟩ := hAI ι v c r hx
  obtain ⟨s, b, w, hw1, hw2⟩ := UpperTheory.hecke_correspondence_product M ⟨D.W, D.π ≫ M.p⟩ D.π rfl j n T hr A hA D.s D.hs (fun i X y hy => D.gen X y hy i) v
  let σ : Fin (n + 1) → ℤ := fun i => (-1) ^ (i : ℕ) * ((l ^ f : ℕ) : ℤ) ^ ((i : ℕ).choose 2)
  have ha : (fun x : (Σ j : Fin (n + 1), Fin (T j).d) => (-1 : ℤ) ^ (x.1 : ℕ) * (((l ^ f) ^ ((x.1 : ℕ).choose 2) : ℕ) : ℤ)) = fun x => σ x.1 := by
    funext x
    simp only [σ]
    push_cast
    rfl
  rw [ha] at hZ
  have hS := siteAnn l (OK l K) M.X M.p g (PX (D.π ≫ M.p) (okToOC l K)) M.P ρ F f (Σ j : Fin (n + 1), Fin (T j).d) (fun x => σ x.1)
    (fun x => pxMap (okToOC l K) (D.s x.1 x.2 ≫ (T x.1).r) (by rw [Category.assoc, hr, ← Category.assoc, D.hs]))
    (fun x => n - x.1 + N0) hZ
  have hV := levZero he M ⟨D.W, D.π ≫ M.p⟩ D.π rfl j n f N0 N1 r s b a u (Fintype.card (∀ i, Equiv.Perm (Fin (T i).d)))
    (d := fun i => (T i).d) (fun i x => D.s i x ≫ (T i).r) (fun i x => by
      change (D.s i x ≫ (T i).r) ≫ M.p = D.π ≫ M.p
      rw [Category.assoc, hr, ← Category.assoc, D.hs]) v c w σ
    (fun lev => pullH ρ lev j (X lev))
    (fun lev y hy => avgMH l _ _ _ _ _ hgp lev j y hy)
    (fun lev => hS lev j (X lev) (hX lev).1) (fun lev => (hX lev).2) hw2
  have h0 := hInj (Fin (n + 1) × ι) (fun q => w q.1 q.2) _ u hV
  have hκ : Fintype.card (∀ i, Equiv.Perm (Fin (T i).d)) * l ^ (a + f * (n + N0) * u) * l ^ b ≠ 0 :=
    mul_ne_zero (mul_ne_zero Fintype.card_ne_zero (pow_ne_zero _ (Fact.out : l.Prime).ne_zero)) (pow_ne_zero _ (Fact.out : l.Prime).ne_zero)
  exact UpperTheory.crystalline_expansion_relation_of_scaled_endomorphisms B M j f n (N0 + N1) r s _ hκ A v c w σ hw1 h0

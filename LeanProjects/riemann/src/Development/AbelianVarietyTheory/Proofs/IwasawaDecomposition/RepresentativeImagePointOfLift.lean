import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LiftsInvOne
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsPointOfDecoratedLatticeSplicedAtPlace
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ResidueEqZeroIff
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TrueColumnSpacesStandardInFrameCoords
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LevOkTwists
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StepLevelContainsDeepCongruenceAtBadPrime
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.LevelNotMemRowSG
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.ExistsIntegralMulOrderElement
import Formalism.LocalToGlobal.Columns.RecLevelLocP
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LevelElementAtBadPrimesIntegralAndNear
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SupportedUnitaryAdelicIntegralWithInverseStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LevelPrimePrimesNotOverBadPrimePlaceStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.AdT Matrix
open scoped TensorProduct
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.Mem.Col2.LevLiftPt

theorem isPtOf_mul_fr {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [StarRing E]
    {hc : CMData F E} {n : ℕ} {ST SG Q : Finset (HeightOneSpectrum (𝓞 E))} {g m : GL (Fin n) (AfE F E)}
    {p : DecoF E n ST SG Q} (hg : IsPtOf hc g p)
    (hm : m ∈ Formalism.L2.Herm.UstdAf hc n) (h1 : ∀ i j, (m : Matrix (Fin n) (Fin n) (AfE F E)) i j ∈ RInt F E)
    (h2 : ∀ i j, ((m⁻¹ : GL (Fin n) (AfE F E)) : Matrix (Fin n) (Fin n) (AfE F E)) i j ∈ RInt F E)
    (hT : ∀ P ∈ ST, ∀ i j, adAt F P ((m : Matrix (Fin n) (Fin n) (AfE F E)) i j) =
      adAt F P (((1 : GL (Fin n) (AfE F E)) : Matrix (Fin n) (Fin n) (AfE F E)) i j))
    {h : GLG E n SG} (hh : ∀ w : SG, LevRead.IsRed w.1 m (h w)) (c : GLQ E n Q)
    (hfr : ∀ (P : Q) (i j : Fin n), adAt F P.1 (((g * m⁻¹ : GL (Fin n) (AfE F E)) : Matrix (Fin n) (Fin n) (AfE F E)) i j) =
      algebraMap E _ ((p.fr P * ((c P)⁻¹ : GLint E n P.1).1) (Pi.single j 1) i)) :
    IsPtOf hc (g * m⁻¹) (((1, h, c) : UF E n × GLG E n SG × GLQ E n Q) • p) := by
  have hg0 : IsPtOf hc g (ChTwRead.noFr p) :=
    ⟨hg.uni, hg.lat, hg.f, hg.be, fun P => absurd P.2 (Finset.notMem_empty _)⟩
  have H := LevRead.isPtOf_mul (Q := ∅) (fun P => Finset.notMem_empty P) hg0 hm h1 h2 hT hh
    (fun P => absurd P.2 (Finset.notMem_empty _))
  refine ⟨H.uni, H.lat, H.f, H.be, fun P i j => ?_⟩
  rw [hfr P i j]
  rfl

theorem int_of_split : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [StarRing E] (hc : CMData F E) {n : ℕ} (u : GL (Fin n) (AfE F E)), u ∈ Formalism.L2.Herm.UstdAf hc n → ∀ (v : HeightOneSpectrum (𝓞 F)) (P : HeightOneSpectrum (𝓞 E)), Formalism.L2.Col.IsOver v P → (∀ v', v' ≠ v → bc (prV (E := E) v') u = 1) → ∀ g ∈ Formalism.L2.Col.GLint E n P, (∀ r s, adAt F P ((u : Matrix (Fin n) (Fin n) (AfE F E)) r s) = algebraMap E (P.adicCompletion E) (LinearMap.toMatrix' g.toLinearMap r s)) → ∀ i j, (u : Matrix (Fin n) (Fin n) (AfE F E)) i j ∈ RInt F E ∧ ((u⁻¹ : GL (Fin n) (AfE F E)) : Matrix (Fin n) (Fin n) (AfE F E)) i j ∈ RInt F E :=
  GlobalTheory.T.supported_unitary_adelic_integral_with_inverse

theorem vT_notOver : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → ∀ (a : I.ι) (P : SBof I a) (v : HeightOneSpectrum (𝓞 B.host.F)), Formalism.L2.Col.IsOver v P.1 → ∀ (u : B.Word), ∀ P' ∈ (B.primes X).vT u, ¬ Formalism.L2.Col.IsOver v P' :=
  GlobalTheory.T.levelPrime_primes_not_over_bad_prime_place

theorem isRed_of_red : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [StarRing E] {n : ℕ} (P : HeightOneSpectrum (𝓞 E)), ∀ g ∈ Formalism.L2.Col.GLint E n P, ∀ (A : Matrix (Fin n) (Fin n) (𝓞 E ⧸ P.asIdeal)), (∀ y ∈ Formalism.L2.Col.stdAt E n P, redV P (g y) = A.mulVec (redV P y)) → ∀ (m : GL (Fin n) (AfE F E)), (∀ r s, adAt F P ((m : Matrix (Fin n) (Fin n) (AfE F E)) r s) = algebraMap E (P.adicCompletion E) (LinearMap.toMatrix' g.toLinearMap r s)) → LevRead.IsRed P m A := by
  intro F E _ _ _ _ _ _ n P g hg A hA m hm r s
  have h := ReadBad.isRed_ratA (F := F) hg hA r s
  have e : adAt F P (((GlobalTheory.TwU.ratA F (toGLm E n g) : GL (Fin n) (AfE F E)) : Matrix (Fin n) (Fin n) (AfE F E)) r s) =
      algebraMap E (P.adicCompletion E) (LinearMap.toMatrix' g.toLinearMap r s) := by
    show adAt F P (Formalism.UG.inclE (F := F) (FiniteAdeleRing (𝓞 F) F) _) = _
    rw [adAt_inclE]
    rfl
  show HasRes P _ _
  rw [hm r s, ← e]
  exact h

theorem adAt_of_off {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [StarRing E] {n : ℕ}
    {u : GL (Fin n) (AfE F E)} {v : HeightOneSpectrum (𝓞 F)} (hoff : ∀ v', v' ≠ v → bc (prV (E := E) v') u = 1)
    {Q : HeightOneSpectrum (𝓞 E)} (hQ : ¬ Formalism.L2.Col.IsOver v Q) (i j : Fin n) :
    adAt F Q ((u : Matrix (Fin n) (Fin n) (AfE F E)) i j) =
      adAt F Q (((1 : GL (Fin n) (AfE F E)) : Matrix (Fin n) (Fin n) (AfE F E)) i j) := by
  have hne : Q.under (𝓞 F) ≠ v := by
    rintro rfl
    exact hQ rfl
  refine ChTwRead.adAt_congr_prV Q ?_
  have h1 := congrArg (fun g : GL (Fin n) (E ⊗[F] (Q.under (𝓞 F)).adicCompletion F) => g.val i j) (hoff _ hne)
  have h2 := congrArg (fun g : GL (Fin n) (E ⊗[F] (Q.under (𝓞 F)).adicCompletion F) => g.val i j)
    (map_one (bc (prV (E := E) (Q.under (𝓞 F)))) : bc (prV (E := E) (Q.under (𝓞 F))) (1 : GL (Fin n) (AfE F E)) = 1)
  exact h1.trans h2.symm

theorem core {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [StarRing E]
    (hc : CMData F E) {n : ℕ} {ST SG Q : Finset (HeightOneSpectrum (𝓞 E))} {g0 x kk : GL (Fin n) (AfE F E)}
    {p : DecoF E n ST SG Q} (hp : IsPtOf hc g0 p) (hx : x ∈ Formalism.L2.Herm.UstdAf hc n) (hk : kk ∈ Formalism.L2.Herm.UstdAf hc n)
    (v : HeightOneSpectrum (𝓞 F)) (P : HeightOneSpectrum (𝓞 E)) (hv : Formalism.L2.Col.IsOver v P)
    (hxoff : ∀ v', v' ≠ v → bc (prV (E := E) v') x = 1) (g' : Sp E n ≃ₗ[E] Sp E n) (hg' : g' ∈ Formalism.L2.Col.GLint E n P)
    (hpt : ∀ r s, adAt F P (((kk⁻¹ * x * kk : GL (Fin n) (AfE F E)) : Matrix (Fin n) (Fin n) (AfE F E)) r s) =
      algebraMap E (P.adicCompletion E) (LinearMap.toMatrix' g'.toLinearMap r s))
    (hST : ∀ P' ∈ ST, ¬ Formalism.L2.Col.IsOver v P') (hover : ∀ w, w ∈ SG ∨ w ∈ Q → Formalism.L2.Col.IsOver v w → w = P)
    (h : GLG E n SG) (c : GLQ E n Q)
    (hG : ∀ hP : P ∈ SG, ∀ y ∈ Formalism.L2.Col.stdAt E n P, redV P (g' y) = ((h ⟨P, hP⟩)⁻¹).1.mulVec (redV P y))
    (hGo : ∀ w : SG, w.1 ≠ P → ∀ y ∈ Formalism.L2.Col.stdAt E n w.1,
      redV w.1 ((1 : Sp E n ≃ₗ[E] Sp E n) y) = ((h w)⁻¹).1.mulVec (redV w.1 y))
    (hQ : ∀ hP : P ∈ Q, g' = ((c ⟨P, hP⟩)⁻¹).1)
    (hQo : ∀ P'' : Q, P''.1 ≠ P → (1 : Sp E n ≃ₗ[E] Sp E n) = ((c P'')⁻¹).1) :
    IsPtOf hc (g0 * (kk⁻¹ * x * kk)) (((1, h, c) : UF E n × GLG E n SG × GLQ E n Q) • p) := by
  set m := kk⁻¹ * x * kk with hm
  have hmU : m ∈ Formalism.L2.Herm.UstdAf hc n := mul_mem (mul_mem (inv_mem hk) hx) hk
  have hmoff : ∀ v', v' ≠ v → bc (prV (E := E) v') m = 1 := fun v' hv' => by
    rw [hm, map_mul, map_mul, map_inv, hxoff v' hv', mul_one, inv_mul_cancel]
  have hmioff : ∀ v', v' ≠ v → bc (prV (E := E) v') m⁻¹ = 1 := fun v' hv' => by
    rw [map_inv, hmoff v' hv', inv_one]
  have hInt := int_of_split hc m hmU v P hv hmoff g' hg' hpt
  have e : g0 * m = g0 * m⁻¹⁻¹ := by rw [inv_inv]
  rw [e]
  refine isPtOf_mul_fr hp (inv_mem hmU) (fun r s => (hInt r s).2) (fun r s => by rw [inv_inv]; exact (hInt r s).1) ?_ ?_ c ?_
  · intro P' hP' r s
    exact adAt_of_off hmioff (hST P' hP') r s
  · intro w
    by_cases hw : w.1 = P
    · obtain ⟨w, hwm⟩ := w
      simp only at hw
      subst hw
      have hC := isRed_of_red w g' hg' _ (hG hwm) m hpt
      obtain ⟨Bm, hB⟩ := LevRead.exists_isRed (x := m⁻¹) (P := w)
        (fun r s => (mem_rInt_iff F E _).1 (hInt r s).2 w)
        (fun r s => by rw [inv_inv]; exact (mem_rInt_iff F E _).1 (hInt r s).1 w)
      have h1 := hC.mul hB
      rw [mul_inv_cancel] at h1
      have h2 := h1.unique LevRead.isRed_one
      have h3 : (h ⟨w, hwm⟩)⁻¹ * Bm = 1 := Units.ext (by rw [Units.val_mul]; exact h2)
      rw [inv_mul_eq_one] at h3
      rw [h3]
      exact hB
    · have hwnot : ¬ Formalism.L2.Col.IsOver v w.1 := fun h' => hw (hover w.1 (Or.inl w.2) h')
      have hC1 := isRed_of_red (F := F) w.1 1 (one_mem _) _ (hGo w hw) (1 : GL (Fin n) (AfE F E)) (fun r s => by
        rw [show LinearMap.toMatrix' (1 : Sp E n ≃ₗ[E] Sp E n).toLinearMap = 1 from LinearMap.toMatrix'_id]
        simp only [Units.val_one, Matrix.one_apply]
        split_ifs <;> simp)
      have h2 := hC1.unique LevRead.isRed_one
      have h3 : (h w)⁻¹ = 1 := Units.ext h2
      rw [inv_eq_one] at h3
      rw [h3]
      intro r s
      rw [adAt_of_off hmioff hwnot r s]
      exact LevRead.isRed_one r s
  · intro P'' r s
    rw [inv_inv, Units.val_mul, Matrix.mul_apply, map_sum]
    by_cases hPP : P''.1 = P
    · obtain ⟨P'', hPm⟩ := P''
      simp only at hPP
      subst hPP
      rw [← hQ hPm]
      simp_rw [map_mul, hp.fr ⟨P'', hPm⟩ r, hpt, ← map_mul]
      rw [← map_sum]
      congr 1
      rw [LinearEquiv.mul_apply]
      conv_rhs => rw [pi_eq_sum_univ (g' (Pi.single s 1)), map_sum]
      simp only [map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, LinearMap.toMatrix'_apply,
        LinearEquiv.coe_coe]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [mul_comm]
      congr 2
      exact congrArg (fun y => p.fr ⟨P'', hPm⟩ y r) (by funext j; simp [Pi.single_apply, eq_comm])
    · have hPnot : ¬ Formalism.L2.Col.IsOver v P''.1 := fun h' => hPP (hover P''.1 (Or.inr P''.2) h')
      rw [← hQo P'' hPP, mul_one]
      simp_rw [map_mul, adAt_of_off hmoff hPnot]
      simp only [Units.val_one, Matrix.one_apply, apply_ite (adAt F P''.1), map_one, map_zero, mul_ite, mul_one, mul_zero,
        Finset.sum_ite_eq', Finset.mem_univ, if_true]
      exact hp.fr P'' r s

theorem mul_conj {G : Type} [Group G] (y x k : G) : y * k * (k⁻¹ * x * k) = y * x * k := by group

set_option maxHeartbeats 1000000 in

theorem pt_of_lift : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι) (i : ℕ) (hi : i ≤ B.R.m) (bad : Set (HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F))) (Ch : Type) (chOf : (I.stp u a i).Cl → Ch) (K : Charts I l Z u a i hi bad chOf) (k : Ch → GA B (B.R.N i)), ReadsAt I l Z K k → ∀ (c : (I.stp u a i).Cl) (kk : GL (Fin ((I.rec7 l Z).R.N i)) (TensorProduct (I.rec7 l Z).host.F (I.rec7 l Z).host.E (FiniteAdeleRing (𝓞 (I.rec7 l Z).host.F) (I.rec7 l Z).host.F))), kk = k (chOf c) → ∀ (P : SBof I a) (v : HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F)), Formalism.L2.Col.IsOver v (GlobalTheory.TwU.seamP (sm I l Z) P.1) → ∀ x ∈ UPts (sigD (I.rec7 l Z)) (gramN (I.rec7 l Z) i hi) (FiniteAdeleRing (𝓞 (I.rec7 l Z).host.F) (I.rec7 l Z).host.F), (∀ v', v' ≠ v → bc (prV (E := (I.rec7 l Z).host.E) v') x = 1) → ∀ g' ∈ Formalism.L2.Col.GLint B.fields.E (B.R.N i) P.1, (∀ r s, adAt (I.rec7 l Z).host.F (GlobalTheory.TwU.seamP (sm I l Z) P.1) ((kk⁻¹ * x * kk).1 r s) = algebraMap (I.rec7 l Z).host.E ((GlobalTheory.TwU.seamP (sm I l Z) P.1).adicCompletion (I.rec7 l Z).host.E) ((GlobalTheory.TwU.seamGL (sm I l Z) g').1 r s)) → ∀ κ' : (I.stp u a i).G c.1, Keeps I κ' ((I.stp u a i).rep c) → LiftsInv I κ' P g' → (∀ P', P' ≠ P → LiftsInv I κ' P' 1) → PtOf (((K (chOf c)).y ⟨c, rfl⟩).1 * x * kk) (((I.stp u a i).act c.1 κ' ((I.stp u a i).rep c)).1.1) := by
  intro B X I hOk hPins l Z u a i hi bad Ch chOf K k hR c kk hkk P v hv x hx hxoff g' hg' hpt κ' hK hLP hLo
  have hseam : GlobalTheory.TwU.seamP (sm I l Z) P.1 = P.1 := by
    ext y
    exact GlobalTheory.TwU.mem_seamP (sm I l Z) P.1 y
  rw [hseam] at hv hpt
  obtain ⟨hLev, hdisj, -⟩ := GlobalTheory.Mem.LevTwist.levOk_twists B X I hOk
  have hd : Disjoint (B.primes X).vGs (I.Q a) := Finset.disjoint_of_subset_right (ColIn.Q_subset_SQ I a) hdisj
  have hp := IsPtOf.of_extTo (ColIn.Q_subset_SQ I a) hd (hR.pt c)
  rw [← hkk] at hp

  obtain ⟨pk, hpk, -⟩ := hR.k_std (chOf c)
  have hk : kk ∈ UAd B.sp.cm (B.R.N i) := hkk ▸ hpk.uni
  have hg1 : gramN (I.rec7 l Z) i hi = 1 := ((GlobalTheory.Mem.Col2.TC.spaces_in_coordinates I hOk hPins l Z).2.2.2 i hi).1
  have hxU : x ∈ UAd B.sp.cm (B.R.N i) := by
    have e : UPts (sigD (I.rec7 l Z)) (gramN (I.rec7 l Z) i hi) (FiniteAdeleRing (𝓞 (I.rec7 l Z).host.F) (I.rec7 l Z).host.F) =
        UAd B.sp.cm (B.R.N i) := by rw [hg1]; rfl
    exact e ▸ hx
  have hγ : κ'.1 = 1 := by
    have h1 : toGLm B.fields.E (B.R.N i) κ'.1.1 = toGLm B.fields.E (B.R.N i) 1 := by
      rw [map_one]
      exact hK.1
    exact Subtype.ext ((toGLm B.fields.E (B.R.N i)).injective h1)
  have hq : ((I.stp u a i).act c.1 κ' ((I.stp u a i).rep c)).1.1 =
      ((1, fun w => (κ'.2.1.1 w), κ'.2.2.1) : UF B.fields.E (B.R.N i) × GLG B.fields.E (B.R.N i) (B.primes X).vGs × GLQ B.fields.E (B.R.N i) (I.Q a)) • ((I.stp u a i).rep c).1.1 := by
    show FrmG.incl _ _ κ' • _ = _
    rw [← hγ]
    rfl

  have hPu : P.1 ∈ uSG (B.primes X).vGs I.SQ := by
    have h := P.2
    simp only [uSG, Finset.mem_union] at h ⊢
    rcases h with h | h
    · exact Or.inl h
    · exact Or.inr (ColIn.Q_subset_SQ I a h)
  have hS : ∀ w, w ∈ (B.primes X).vGs ∨ w ∈ I.Q a → w ∈ SBof I a := by
    intro w hw
    show w ∈ uSG _ _
    simp only [uSG, Finset.mem_union]
    exact hw
  have key := core B.sp.cm hp hxU hk v P.1 hv hxoff g' hg' hpt (vT_notOver I hOk a P v hv u) (fun w hw hwv => by
      have hw' : w ∈ uSG (B.primes X).vGs I.SQ := by
        simp only [uSG, Finset.mem_union]
        rcases hw with h | h
        · exact Or.inl h
        · exact Or.inr (ColIn.Q_subset_SQ I a h)
      rcases rll_over_cases B.sp.cm hv hwv with h | h
      · exact h
      · exact absurd (h ▸ hw') (hLev.split P.1 hPu))
    (fun w => κ'.2.1.1 w) κ'.2.2.1 hLP.2.1
    (fun w hw => (hLo ⟨w.1, hS w.1 (Or.inl w.2)⟩ (fun e => hw (congrArg Subtype.val e))).2.1 w.2)
    hLP.2.2
    (fun P'' hP'' => (hLo ⟨P''.1, hS P''.1 (Or.inr P''.2)⟩ (fun e => hP'' (congrArg Subtype.val e))).2.2 P''.2)
  have e := mul_conj (G := GA B (B.R.N i)) ((K (chOf c)).y ⟨c, rfl⟩).1 x kk
  rw [hq]
  exact e ▸ key

end GlobalTheory.Mem.Col2.LevLiftPt

end

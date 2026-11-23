import Development.WeilBound.CoreStatements.MinimalPrimeDimensions.RangeOfMemSupportPush
import Development.WeilBound.CoreStatements.MinimalPrimeDimensions.FinrankEqOfDimZero
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TopologicalKrullDimLeZeroOfSubset
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsChowDegreeSection
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsChowDegreeClosedPoint
import GroundTheory.HeightsAndTheta.Heights.ChowForms.PConeDimComponent

set_option autoImplicit false
set_option linter.style.haveILetI false

noncomputable section

open CategoryTheory AlgebraicGeometry NumberField MvPolynomial IsDedekindDomain TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier
open GroundTheory.Heights₂.Heights (IsProjPrime IsHomogIdeal IsRelevant relComps localMult chowDegree reduceMod divCycle)

namespace ChowFormHeightComparison₂.CF.V

open GroundTheory.Heights₂.Heights.ObjectsChow (ChowDegreeSection.Statement ChowDegreeClosedPoint.Statement)

theorem dim_closure_add_one_le {Z : Scheme.{0}} {z z' : Z} (h : z' ⤳ z) (hne : z ≠ z') :
    topologicalKrullDim (closure {z} : Set Z) + 1 ≤ topologicalKrullDim (closure {z'} : Set Z) :=
  topologicalKrullDim_add_one_le isClosed_closure isClosed_closure fun x hx =>
    ⟨z', subset_closure rfl, fun h' => hne (h.antisymm (specializes_iff_mem_closure.2 h')).eq.symm,
      h.trans (specializes_iff_mem_closure.2 hx)⟩

theorem dim_closure_eq {Y Z : Scheme.{0}} [IsIntegral Y] (i : Y ⟶ Z) [IsClosedImmersion i] :
    topologicalKrullDim (closure {i (genericPoint Y)} : Set Z) = topologicalKrullDim Y := by
  have h₁ := (genericPoint_spec Y).image i.continuous
  rw [Set.image_univ, i.isClosedEmbedding.isClosed_range.closure_eq] at h₁
  exact topologicalKrullDim_eq_of_isEmbedding i.isClosedEmbedding.isEmbedding h₁.def.symm

theorem length_cut {Z : Scheme.{0}} [IsIntegral Z] [IsLocallyNoetherian Z] {B : LB Z} (hB : B.IsLB) (s : B.Sec)
    (hs : genericPoint Z ∈ nonzeroLocus s) {z : Z} (hz : (divOfSec hB s hs).mult z ≠ 0) :
    ((Module.length (Z.presheaf.stalk z) ((cut (GlobalTheory.structureModule Z) hB s).presheaf.stalk z :)).toNat : ℤ) =
      (divOfSec hB s hs).mult z := by
  obtain ⟨i, hi⟩ := LB.mem_of_cover hB z
  obtain ⟨q⟩ := CutDegree.nonempty_stalk_cut_equiv (GlobalTheory.structureModule Z) hB s i hi
  rw [mult_divOfSec (CartierDiv.coheight_eq_one_of_mult_ne_zero hz) hi, ← q.length_eq]
  refine congrArg (fun n : ℕ∞ => (n.toNat : ℤ)) (Submodule.Quotient.equiv _ _ (QCoh.structureModuleStalkEquiv z) ?_).length_eq
  rw [Submodule.map_pointwise_smul, Submodule.map_top, LinearEquiv.range, ← Submodule.ideal_span_singleton_smul,
    smul_eq_mul, Ideal.mul_top]

variable {κ : Type} [Field κ] {m : ℕ}

theorem isRelevant_of_dim {W : Ideal (MvPolynomial (Fin m) κ)}
    (hW : W ≤ RingHom.ker (constantCoeff : MvPolynomial (Fin m) κ →+* κ))
    (hd : ringKrullDim (MvPolynomial (Fin m) κ ⧸ W) ≠ 0) : IsRelevant W := by
  by_contra h
  have hX : ∀ j, X j ∈ W := fun j => by_contra fun hj => h ⟨j, hj⟩
  have key (g : MvPolynomial (Fin m) κ) : g - C (constantCoeff g) ∈ W := by
    induction g using MvPolynomial.induction_on with
    | C a => simp
    | add a b ha hb =>
      have := W.add_mem ha hb
      rwa [sub_add_sub_comm, ← map_add, ← map_add] at this
    | mul_X a j _ => simpa using W.mul_mem_left a (hX j)
  have e : W = RingHom.ker (constantCoeff : MvPolynomial (Fin m) κ →+* κ) := le_antisymm hW fun g hg => by
    have := key g
    rwa [(RingHom.mem_ker).1 hg, map_zero, sub_zero] at this
  have : W.IsMaximal := e ▸ RingHom.ker_isMaximal_of_surjective _ fun a => ⟨C a, by simp⟩
  exact hd (ringKrullDim_eq_zero_of_isField ((Ideal.Quotient.maximal_ideal_iff_isField_quotient W).1 this))

theorem field_case (h1 : StPts) (h2 : StPull) (h3 : StDiv) (hS : ChowDegreeSection.Statement)
    (hP : ChowDegreeClosedPoint.Statement) [PerfectField κ] (e : ℕ) :
    ∀ (Z : Scheme.{0}) [IsIntegral Z] [Algebra κ Γ(Z, ⊤)] (B : LB Z) (s : Fin m → B.Sec),
      IsProjOver (strHom κ Z) → Emb (strHom κ Z) s →
      ringKrullDim (MvPolynomial (Fin m) κ ⧸ ptIdeal (strHom κ Z) s (genericPoint Z)) = (e + 1 : ℕ) →
      topologicalKrullDim Z = e ∧
        topSelfIntersection κ B e = chowDegree (ptIdeal (strHom κ Z) s (genericPoint Z)) (e + 1) := by
  classical
  have hC := GroundTheory.Heights₂.Heights.ConeDimComponent.proof_closed
  induction e with
  | zero =>
    intro Z _ _ B s hp hE hd
    have := isNoetherian_of_isProjOver hp
    obtain ⟨a, b, c, d⟩ := h1 κ Z _ B m s hE
    obtain ⟨k, hk⟩ := Opens.mem_iSup.1 (hE.cover.ge (Opens.mem_top (genericPoint Z)))
    have hX := (d _ _ (isComb_single _ s k) _).1 hk
    rw [linForm_single] at hX
    have h0 : topologicalKrullDim Z ≤ 0 := ENat.WithBot.add_le_add_one_right_iff.1
      ((dim_add_one_le h1 hE).trans (hd.trans (by simp)).le)
    have : Nonempty (IrreducibleCloseds Z) := ⟨⟨Set.univ, IrreducibleSpace.isIrreducible_univ Z, isClosed_univ⟩⟩
    refine ⟨le_antisymm h0 Order.krullDim_nonneg, ?_⟩
    rw [hP κ m _ k (a _) hd hX, finrank_eq_of_dim_zero hE h0 hk, topSelf_def, interNum_of_isEmpty,
      chi_eq_hdim_zero_of_suppDim_le_zero κ (QCoh.suppDim_structureModule.trans_le h0),
      ← ((coh.zeroUnitEquiv Z).restrictScalars κ).finrank_eq]
    rfl
  | succ e ih =>
    intro Z _ _ B s hp hE hd
    have := isNoetherian_of_isProjOver hp
    obtain ⟨a, b, c, d⟩ := h1 κ Z _ B m s hE
    obtain ⟨k, hk⟩ := Opens.mem_iSup.1 (hE.cover.ge (Opens.mem_top (genericPoint Z)))
    have hu := isComb_single (strHom κ Z) s k
    have hX := (d _ _ hu _).1 hk
    obtain ⟨d₁, d₂⟩ := h3 κ Z _ B m s hE _ _ hu hk
    have hsec := hS κ m e _ _ (a _) hd hX
    have hcomp := fun W => hC κ m (e + 1) _ W _ (a _) hd hX
    generalize (Pi.single k 1 : Fin m → κ) = u at *
    set P := ptIdeal (strHom κ Z) s with hPdef
    set J := P (genericPoint Z) ⊔ Ideal.span {GroundTheory.Heights₂.Heights.linForm u} with hJ
    let T := (divOfSec hE.isLB (s k) hk).finite_support_mult.toFinset
    have hT (z : Z) : z ∈ T ↔ (divOfSec hE.isLB (s k) hk).mult z ≠ 0 := Set.Finite.mem_toFinset _
    have inj {z z' : Z} (h : P z = P z') : z = z' := (((b _ _).2 h.le).antisymm ((b _ _).2 h.ge)).eq
    have hex (W) (hW : W ∈ relComps J) : ∃ z ∈ T, P z = W := by
      obtain ⟨z, rfl⟩ := c W (hcomp W hW).1 (le_sup_left.trans hW.1.1.2)
      exact ⟨z, (hT z).2 ((d₁ z).2 hW), rfl⟩
    have key : ∀ (Y : Scheme.{0}) (i : Y ⟶ Z) [IsClosedImmersion i] [IsIntegral Y] [Algebra κ Γ(Y, ⊤)],
        (∀ r : κ, i.appTop (algebraMap κ Γ(Z, ⊤) r) = algebraMap κ Γ(Y, ⊤) r) → i (genericPoint Y) ∈ T →
        topologicalKrullDim Y = e ∧ topSelfIntersection κ (B.pull i) e = chowDegree (P (i (genericPoint Y))) (e + 1) := by
      intro Y i _ _ _ hi hz
      obtain ⟨E', pt', -⟩ := h2 κ Z Y _ B m s i hE
      have hp' := ProjSpace.isProjOver_comp_of_isClosedImmersion i hp
      rw [comp_strHom hi] at E' pt' hp'
      have := ih Y _ _ hp' E' (by rw [pt']; exact (hcomp _ ((d₁ _).1 ((hT _).1 hz))).2)
      rwa [pt'] at this
    have hTd : ∀ z ∈ T, topologicalKrullDim (closure {z} : Set Z) = e := fun z hz => by
      obtain ⟨Y, i, _, _, rfl⟩ := exists_isClosedImmersion_genericPoint z
      letI := algebraΓAlong κ i
      exact (dim_closure_eq i).trans (key Y i (appTop_algebraMap_along κ i) hz).1
    have hmem (z : Z) (hz : z ∉ nonzeroLocus (s k)) : J ≤ P z :=
      sup_le ((b _ _).1 (genericPoint_specializes z))
        ((Ideal.span_singleton_le_iff_mem _).2 (by_contra fun h => hz ((d _ _ hu z).2 h)))
    have hSd : ∀ z ∈ ((nonzeroLocus (s k) : Set Z)ᶜ), z ∉ T → topologicalKrullDim (closure {z} : Set Z) < e := by
      intro z hz hzT
      have := (a z).isPrime
      obtain ⟨W, hW, hle⟩ := Ideal.exists_minimalPrimes_le (hmem z hz)
      obtain ⟨j, hj⟩ := (a z).isRelevant
      obtain ⟨z', hz', rfl⟩ := hex W ⟨hW, j, fun h => hj (hle h)⟩
      have h4 := dim_closure_add_one_le ((b _ _).2 hle) fun h => hzT (h ▸ hz')
      rw [hTd z' hz'] at h4
      by_contra hc
      rw [not_lt] at hc
      have h5 : e + 1 ≤ e := by exact_mod_cast (add_le_add_left hc 1).trans h4
      omega
    refine ⟨le_antisymm (ENat.WithBot.add_le_add_one_right_iff.1
      ((dim_add_one_le h1 hE).trans (hd.trans (Nat.cast_succ _)).le)) ?_, ?_⟩
    · have hm : J ≤ RingHom.ker (constantCoeff : MvPolynomial (Fin m) κ →+* κ) :=
        sup_le (le_ker_constantCoeff (a _)) ((Ideal.span_singleton_le_iff_mem _).2 (by
          simp [RingHom.mem_ker, GroundTheory.Heights₂.Heights.linForm]))
      have := RingHom.ker_isPrime (constantCoeff : MvPolynomial (Fin m) κ →+* κ)
      have := (a (genericPoint Z)).isPrime
      obtain ⟨W, hW, hle⟩ := Ideal.exists_minimalPrimes_le hm
      have h4 := ringKrullDim_quotient_add_one_of_mem_minimalPrimes_sup κ hX hW
      obtain ⟨z, hz, rfl⟩ := hex W ⟨hW, isRelevant_of_dim hle fun h0 => by
        rw [h0, hd] at h4
        have h5 : 0 + 1 = e + 1 + 1 := by exact_mod_cast h4
        omega⟩
      have h5 := dim_closure_add_one_le (genericPoint_specializes z) fun h =>
        hX (h ▸ hW.1.2 (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _)))
      rw [hTd z hz] at h5
      exact (Nat.cast_succ e).le.trans (h5.trans (topologicalKrullDim_subspace_le Z _))
    · have hf := algebraMap_eq_strHom κ Z
      have := (mono_cutHom_structureModule_iff hE.isLB (s k)).2 hk
      have e₁ : (fun _ : Fin (e + 1) => B) = (Fin.cons B (fun _ => B) : Fin (e + 1) → LB Z) :=
        funext (Fin.cases rfl fun _ => rfl)
      have e₂ := (interNum_eq_sum hp (P := fun _ : Fin e => B) (fun _ => hE.isLB) _ T
        (fun z => chowDegree (P z) (e + 1)) hTd hSd (fun Y i _ _ _ hi hz => (key Y i hi hz).2)
        (cut (GlobalTheory.structureModule Z) hE.isLB (s k)) inferInstance
        (by rw [support_cut]; exact fun x hx => hx.2)).2
      rw [topSelf_def, e₁, interNum_cons_eq_interNum_cut hE.isLB (s k) (fun _ => hE.isLB)
        (finiteCohTwists_of_isProjOver hf _ hp), e₂]
      show _ = ((chowDegree _ (e + 2) : ℕ) : ℤ)
      rw [hsec, Finsupp.sum, Nat.cast_sum]
      have hval (z : Z) (hz : z ∈ T) : ((divCycle (P (genericPoint Z)) u (P z) : ℕ) : ℤ) =
          (divOfSec hE.isLB (s k) hk).mult z := by
        rw [d₂ z ((hT z).1 hz), divCycle, GroundTheory.Heights₂.Heights.fundCycle, Finsupp.onFinset_apply,
          if_pos ((d₁ z).1 ((hT z).1 hz))]
      refine Finset.sum_bij (fun z _ => P z) (fun z hz => ?_) (fun _ _ _ _ h => inj h) (fun W hW => ?_)
        fun z hz => ?_
      · rw [Finsupp.mem_support_iff, ← Nat.cast_ne_zero (R := ℤ), hval z hz]
        exact (hT z).1 hz
      · obtain ⟨z, hz, rfl⟩ := hex W (by
          by_contra h
          rw [Finsupp.mem_support_iff, divCycle, GroundTheory.Heights₂.Heights.fundCycle, Finsupp.onFinset_apply,
            if_neg h] at hW
          exact hW rfl)
        exact ⟨z, hz, rfl⟩
      · rw [length_cut hE.isLB (s k) hk ((hT z).1 hz), Nat.cast_mul, hval z hz]

end ChowFormHeightComparison₂.CF.V

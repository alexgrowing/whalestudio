import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.CoeffRingsHaveRootsOfUnity
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TypeSpaceProjectionEigenOfLocalisedFormsSection
open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.L2 NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module Polynomial GlobalTheory.Pass GlobalTheory.PendOf

noncomputable section

namespace GlobalTheory.PendOf.EigSpanProof

section GroupAlg

variable {R : Type} [CommRing R] {G : Type} [Group G] [Fintype G]

def conjSum (w : MonoidAlgebra R G) : MonoidAlgebra R G :=
  ∑ h : G, MonoidAlgebra.of R G h * w * MonoidAlgebra.of R G h⁻¹

theorem conjSum_comm_of (w : MonoidAlgebra R G) (m : G) :
    conjSum w * MonoidAlgebra.of R G m = MonoidAlgebra.of R G m * conjSum w := by
  unfold conjSum
  rw [Finset.sum_mul, Finset.mul_sum, ← Equiv.sum_comp (Equiv.mulLeft m)]
  refine Finset.sum_congr rfl fun h _ => ?_
  have hm : MonoidAlgebra.of R G m⁻¹ * MonoidAlgebra.of R G m = 1 := by
    rw [← map_mul, inv_mul_cancel, map_one]
  simp only [Equiv.coe_mulLeft, mul_inv_rev, map_mul, mul_assoc, hm, mul_one]

theorem conjSum_mem_center (w : MonoidAlgebra R G) :
    conjSum w ∈ Subalgebra.center R (MonoidAlgebra R G) := by
  rw [Subalgebra.mem_center_iff]
  intro a
  induction a using MonoidAlgebra.induction_on with
  | of m => exact (conjSum_comm_of w m).symm
  | add x y hx hy => rw [add_mul, mul_add, hx, hy]
  | smul r x hx => rw [smul_mul_assoc, mul_smul_comm, hx]

theorem conjSum_add (x y : MonoidAlgebra R G) : conjSum (x + y) = conjSum x + conjSum y := by
  simp only [conjSum, mul_add, add_mul, Finset.sum_add_distrib]

theorem conjSum_smul (r : R) (x : MonoidAlgebra R G) : conjSum (r • x) = r • conjSum x := by
  simp only [conjSum, Finset.smul_sum, mul_smul_comm, smul_mul_assoc]

theorem conjSum_of_central (z : MonoidAlgebra R G) (hz : ∀ a, z * a = a * z) :
    conjSum z = Fintype.card G • z := by
  unfold conjSum
  have e : ∀ h : G, MonoidAlgebra.of R G h * z * MonoidAlgebra.of R G h⁻¹ = z := fun h => by
    rw [mul_assoc, hz, ← mul_assoc, ← map_mul, mul_inv_cancel, map_one, one_mul]
  simp only [e, Finset.sum_const, Finset.card_univ]

theorem mapCoef_conjSum {S : Type} [CommRing S] (f : R →+* S) (w : MonoidAlgebra R G) :
    PairedCharacterCondition.mapCoef f (conjSum w) = conjSum (PairedCharacterCondition.mapCoef f w) := by
  show MonoidAlgebra.mapRingHom G f (conjSum w) = conjSum (MonoidAlgebra.mapRingHom G f w)
  simp only [conjSum, map_sum, map_mul, MonoidAlgebra.of_apply, MonoidAlgebra.mapRingHom_single, map_one]

theorem mapCoef_of {S : Type} [CommRing S] (f : R →+* S) (m : G) :
    PairedCharacterCondition.mapCoef f (MonoidAlgebra.of R G m) = MonoidAlgebra.of S G m := by
  show MonoidAlgebra.mapRingHom G f _ = _
  simp only [MonoidAlgebra.of_apply, MonoidAlgebra.mapRingHom_single, map_one]

theorem mapCoef_central {S : Type} [CommRing S] (f : R →+* S) (z : MonoidAlgebra R G)
    (hz : z ∈ Subalgebra.center R (MonoidAlgebra R G)) :
    PairedCharacterCondition.mapCoef f z ∈ Subalgebra.center S (MonoidAlgebra S G) := by
  rw [Subalgebra.mem_center_iff] at hz ⊢
  intro a
  induction a using MonoidAlgebra.induction_on with
  | of m =>
    rw [← mapCoef_of f m]
    show MonoidAlgebra.mapRingHom G f _ * MonoidAlgebra.mapRingHom G f _ =
      MonoidAlgebra.mapRingHom G f _ * MonoidAlgebra.mapRingHom G f _
    rw [← map_mul, ← map_mul, hz]
  | add x y hx hy => rw [add_mul, mul_add, hx, hy]
  | smul r x hx => rw [smul_mul_assoc, mul_smul_comm, hx]

theorem mapCoef_smul {S : Type} [CommRing S] (f : R →+* S) (r : R) (x : MonoidAlgebra R G) :
    PairedCharacterCondition.mapCoef f (r • x) = f r • PairedCharacterCondition.mapCoef f x := by
  ext g
  simp [PairedCharacterCondition.mapCoef]

theorem mapCoef_add {S : Type} [CommRing S] (f : R →+* S) (x y : MonoidAlgebra R G) :
    PairedCharacterCondition.mapCoef f (x + y) = PairedCharacterCondition.mapCoef f x + PairedCharacterCondition.mapCoef f y :=
  map_add (MonoidAlgebra.mapRingHom G f) x y

end GroupAlg

section Forms

variable {D : D7}

theorem onMt_add (i : D.nd.Loc) {a b : MonoidAlgebra ℂ (G0g D.nd)}
    (ha : a ∈ Subalgebra.center ℂ (MonoidAlgebra ℂ (G0g D.nd)))
    (hb : b ∈ Subalgebra.center ℂ (MonoidAlgebra ℂ (G0g D.nd))) :
    D.ntypes.onMt (D.nd.mu i) (D.nd.j i) (a + b) =
      D.ntypes.onMt (D.nd.mu i) (D.nd.j i) a + D.ntypes.onMt (D.nd.mu i) (D.nd.j i) b := by
  unfold NTypes.onMt
  rw [dif_pos ha, dif_pos hb, dif_pos (add_mem ha hb), ← map_add]
  rfl

theorem onMt_smul (i : D.nd.Loc) (c : ℂ) {a : MonoidAlgebra ℂ (G0g D.nd)}
    (ha : a ∈ Subalgebra.center ℂ (MonoidAlgebra ℂ (G0g D.nd))) :
    D.ntypes.onMt (D.nd.mu i) (D.nd.j i) (c • a) = c • D.ntypes.onMt (D.nd.mu i) (D.nd.j i) a := by
  unfold NTypes.onMt
  rw [dif_pos ha, dif_pos (Subalgebra.smul_mem _ ha c), ← map_smul]
  rfl

theorem onMt_typeSum (hC : OnMtPreservesTypeV D) (i : D.nd.Loc) (z : MonoidAlgebra ℂ (G0g D.nd))
    (o : Option (D.nd.X i)) :
    typeSum D i o ≤ (typeSum D i o).comap (D.ntypes.onMt (D.nd.mu i) (D.nd.j i) z) := by
  refine iSup₂_le fun P hP F hF => ?_
  exact Submodule.mem_comap.2 (le_biSup (D.naut.typeV i) hP (hC i P z F hF))

def ptPart (D : D7) (i : D.nd.Loc) : Submodule ℂ (D.what₂.Mt (D.nd.mu i) (D.nd.j i)) :=
  ⨆ (o : Option (D.nd.X i)) (_ : o ≠ none), typeSum D i o

theorem onMt_ptPart (hC : OnMtPreservesTypeV D) (i : D.nd.Loc) (z : MonoidAlgebra ℂ (G0g D.nd)) :
    ptPart D i ≤ (ptPart D i).comap (D.ntypes.onMt (D.nd.mu i) (D.nd.j i) z) :=
  iSup₂_le fun o ho F hF => Submodule.mem_comap.2
    (Submodule.mem_iSup_of_mem o (Submodule.mem_iSup_of_mem ho (onMt_typeSum hC i z o hF)))

theorem Phi_mem {i : D.nd.Loc} (s : Sec D i) (w : TensorProduct (D.nd.O i) (KK D.nd i) (D.nd.Mt i)) :
    s.Φ w ∈ ptPart D i := by
  have hw : w ∈ ⨆ x, heckeEig (D.nd.T i) (D.nd.act i) x := by
    rw [Formalism.MainNotions.TruncatedSeriesCountingIdentities.Br.EigSpan_holds D.nd i]; exact Submodule.mem_top
  refine Submodule.iSup_induction _ (motive := fun w => s.Φ w ∈ ptPart D i) hw
    (fun x v hv => ?_) (by rw [map_zero]; exact Submodule.zero_mem _)
    (fun v v' h h' => by rw [map_add]; exact Submodule.add_mem _ h h')
  exact Submodule.mem_iSup_of_mem (some x)
    (Submodule.mem_iSup_of_mem (Option.some_ne_none x) (s.eig x v hv))

theorem class_step (P : PairedCharacterCondition.Pend D) (hC : OnMtPreservesTypeV D) (i : D.nd.Loc) (s : Sec D i)
    (C : ↥(Subalgebra.center (D.nd.O i) (MonoidAlgebra (D.nd.O i) (G0g D.nd))))
    (CL : MonoidAlgebra D.what₂.LL (G0g D.nd)) (hCL : ∀ a, CL * a = a * CL)
    (heq : PairedCharacterCondition.mapCoef D.what₂.embLL CL =
      PairedCharacterCondition.mapCoef (iotaO D.nd D.naut i) (C : MonoidAlgebra (D.nd.O i) (G0g D.nd)))
    (w : TensorProduct (D.nd.O i) (KK D.nd i) (D.nd.Mt i)) :
    s.Φ ((P.zO i C).baseChange (KK D.nd i) w) =
      D.ntypes.onMt (D.nd.mu i) (D.nd.j i)
        (PairedCharacterCondition.mapCoef (iotaO D.nd D.naut i) (C : MonoidAlgebra (D.nd.O i) (G0g D.nd))) (s.Φ w) := by
  set T := D.ntypes.onMt (D.nd.mu i) (D.nd.j i)
    (PairedCharacterCondition.mapCoef (iotaO D.nd D.naut i) (C : MonoidAlgebra (D.nd.O i) (G0g D.nd))) with hT
  have hw : w ∈ Submodule.span (KK D.nd i) (Set.range (D.nd.prMt i)) := by
    rw [D.nd.prMt_span i]; exact Submodule.mem_top
  induction hw using Submodule.span_induction with
  | mem v hv =>
    obtain ⟨y, rfl⟩ := hv
    obtain ⟨y', hy'⟩ := P.zL_stable i CL hCL y
    have hy2 : D.what₂.jMt _ _ y' = T (D.what₂.jMt _ _ y) := by rw [hy', heq]
    rw [← P.zO_act i C y y' hy2]
    have hind := (GlobalTheory.PendOf.PrTypeProof.typeSum_indep D i) none
    have h1 := s.split y
    have h2 := s.split y'
    have hA : s.Φ (D.nd.prMt i y') - T (s.Φ (D.nd.prMt i y)) =
        -((D.what₂.jMt _ _ y' - s.Φ (D.nd.prMt i y')) - T (D.what₂.jMt _ _ y - s.Φ (D.nd.prMt i y))) := by
      rw [map_sub T, ← hy2]; abel
    have m1 : s.Φ (D.nd.prMt i y') - T (s.Φ (D.nd.prMt i y)) ∈ typeSum D i none := by
      rw [hA]; exact Submodule.neg_mem _ (Submodule.sub_mem _ h2 (onMt_typeSum hC i _ none h1))
    have m2 : s.Φ (D.nd.prMt i y') - T (s.Φ (D.nd.prMt i y)) ∈ ptPart D i :=
      Submodule.sub_mem _ (Phi_mem s _) (onMt_ptPart hC i _ (Phi_mem s _))
    exact sub_eq_zero.1 ((Submodule.disjoint_def.1 hind) _ m1 m2)
  | zero => simp only [map_zero]
  | add v v' _ _ h h' => simp only [map_add, h, h']
  | smul a v _ h => rw [LinearMap.map_smul, s.semi, h, s.semi, LinearMap.map_smul]

end Forms

section Main

variable {D : D7}

theorem lhs_smul {i : D.nd.Loc} (s : Sec D i) (r : D.nd.O i) (f : Module.End (D.nd.O i) (D.nd.Mt i))
    (w : TensorProduct (D.nd.O i) (KK D.nd i) (D.nd.Mt i)) :
    s.Φ ((r • f).baseChange (KK D.nd i) w) = iotaO D.nd D.naut i r • s.Φ (f.baseChange (KK D.nd i) w) := by
  rw [LinearMap.baseChange_smul, LinearMap.smul_apply, ← algebraMap_smul (KK D.nd i) r, s.semi]
  rfl

theorem all_central (P : PairedCharacterCondition.Pend D) (hC : OnMtPreservesTypeV D) (i : D.nd.Loc) (s : Sec D i)
    (z : ↥(Subalgebra.center (D.nd.O i) (MonoidAlgebra (D.nd.O i) (G0g D.nd))))
    (w : TensorProduct (D.nd.O i) (KK D.nd i) (D.nd.Mt i)) :
    s.Φ ((P.zO i z).baseChange (KK D.nd i) w) =
      D.ntypes.onMt (D.nd.mu i) (D.nd.j i)
        (PairedCharacterCondition.mapCoef (iotaO D.nd D.naut i) (z : MonoidAlgebra (D.nd.O i) (G0g D.nd))) (s.Φ w) := by
  classical
  haveI : ∀ k, NeZero (D.host.g k) := fun k => ⟨(D.host.g_prime k).ne_zero⟩
  have hQ : ∀ v : MonoidAlgebra (D.nd.O i) (G0g D.nd), ∀ w,
      s.Φ ((P.zO i ⟨conjSum v, conjSum_mem_center v⟩).baseChange (KK D.nd i) w) =
        D.ntypes.onMt (D.nd.mu i) (D.nd.j i) (PairedCharacterCondition.mapCoef (iotaO D.nd D.naut i) (conjSum v)) (s.Φ w) := by
    intro v
    induction v using MonoidAlgebra.induction_on with
    | of m =>
      intro w
      refine class_step P hC i s _ (conjSum (MonoidAlgebra.of D.what₂.LL _ m))
        (fun a => ((Subalgebra.mem_center_iff.1 (conjSum_mem_center _)) a).symm) ?_ w
      show _ = PairedCharacterCondition.mapCoef _ (conjSum _)
      rw [mapCoef_conjSum, mapCoef_conjSum, mapCoef_of, mapCoef_of]
    | add x y hx hy =>
      intro w
      have e : (⟨conjSum (x + y), conjSum_mem_center _⟩ :
          ↥(Subalgebra.center (D.nd.O i) (MonoidAlgebra (D.nd.O i) (G0g D.nd)))) =
          ⟨conjSum x, conjSum_mem_center _⟩ + ⟨conjSum y, conjSum_mem_center _⟩ :=
        Subtype.ext (conjSum_add x y)
      rw [e, map_add, LinearMap.baseChange_add, LinearMap.add_apply, map_add, hx, hy, conjSum_add,
        mapCoef_add, onMt_add i (mapCoef_central _ _ (conjSum_mem_center _))
          (mapCoef_central _ _ (conjSum_mem_center _)), LinearMap.add_apply]
    | smul r x hx =>
      intro w
      have e : (⟨conjSum (r • x), conjSum_mem_center _⟩ :
          ↥(Subalgebra.center (D.nd.O i) (MonoidAlgebra (D.nd.O i) (G0g D.nd)))) =
          r • ⟨conjSum x, conjSum_mem_center _⟩ :=
        Subtype.ext (conjSum_smul r x)
      rw [e, map_smul, lhs_smul, hx, conjSum_smul, mapCoef_smul,
        onMt_smul i _ (mapCoef_central _ _ (conjSum_mem_center _)), LinearMap.smul_apply]
  have hz : ∀ a, (z : MonoidAlgebra (D.nd.O i) (G0g D.nd)) * a = a * z :=
    fun a => ((Subalgebra.mem_center_iff.1 z.2) a).symm
  set n : D.nd.O i := (Fintype.card (G0g D.nd) : D.nd.O i) with hn
  have e : (⟨conjSum (z : MonoidAlgebra (D.nd.O i) (G0g D.nd)), conjSum_mem_center _⟩ :
      ↥(Subalgebra.center (D.nd.O i) (MonoidAlgebra (D.nd.O i) (G0g D.nd)))) = n • z := by
    apply Subtype.ext
    show conjSum (z : MonoidAlgebra (D.nd.O i) (G0g D.nd)) = _
    rw [conjSum_of_central _ hz, ← Nat.cast_smul_eq_nsmul (D.nd.O i)]
    rfl
  have h := hQ z w
  rw [e, map_smul, lhs_smul, hn, conjSum_of_central _ hz, ← Nat.cast_smul_eq_nsmul (D.nd.O i), mapCoef_smul,
    onMt_smul i _ (mapCoef_central _ _ z.2), LinearMap.smul_apply, map_natCast] at h
  have hne : ((Fintype.card (G0g D.nd) : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  exact smul_right_injective _ hne h

theorem main : ∀ (D : D7) (P : PairedCharacterCondition.Pend D), (∀ i, Nonempty (Sec D i)) → OnMtPreservesTypeV D → EigSpan P := by
  intro D P hS hC i z x c hzc u hu
  let s := (hS i).some
  refine s.inj ?_
  have h1 := all_central P hC i s z u
  have h2 : D.ntypes.onMt (D.nd.mu i) (D.nd.j i)
      (PairedCharacterCondition.mapCoef (iotaO D.nd D.naut i) (z : MonoidAlgebra (D.nd.O i) (G0g D.nd))) (s.Φ u) =
      iotaO D.nd D.naut i c • s.Φ u := by
    have hle : typeSum D i (some x) ≤ Module.End.eigenspace (D.ntypes.onMt (D.nd.mu i) (D.nd.j i)
        (PairedCharacterCondition.mapCoef (iotaO D.nd D.naut i) (z : MonoidAlgebra (D.nd.O i) (G0g D.nd)))) (iotaO D.nd D.naut i c) :=
      iSup₂_le fun PI hPI F hF => Module.End.mem_eigenspace_iff.2 (hzc PI hPI F hF)
    exact Module.End.mem_eigenspace_iff.1 (hle (s.eig x u hu))
  rw [h1, h2, ← algebraMap_smul (KK D.nd i) c u, s.semi]
  rfl

end Main

end GlobalTheory.PendOf.EigSpanProof

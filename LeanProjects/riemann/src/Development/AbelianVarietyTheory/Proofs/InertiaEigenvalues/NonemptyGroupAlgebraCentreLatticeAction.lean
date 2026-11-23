import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.CoeffRingsHaveRootsOfUnity
import Formalism.SharpRestriction.LevelLetterCocycles.EndomorphismIndexBound
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ComparisonMapIntertwinesGroupAlgebraActionStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemHeckeEigOfImageMovedByCentreStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CenterMonoidAlgebraLeSpanCentralIntegralStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AddValuationNonnegRingOfIntegersNumberFieldStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CentralIntegralPreservesLocalisedLatticeImageStatement
open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.L2 NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module Polynomial GlobalTheory.Pass GlobalTheory.PendOf Formalism.MainNotions.PairedCharacterCondition
open scoped TensorProduct

noncomputable section
namespace GlobalTheory.CenOAct

theorem mapCoef_eq {A B M : Type} [Semiring A] [Semiring B] [Monoid M] (f : A →+* B) (z : MonoidAlgebra A M) :
    mapCoef f z = MonoidAlgebra.mapRingHom M f z := by
  apply MonoidAlgebra.ext
  ext g
  simp [mapCoef, MonoidAlgebra.coeff_mapRingHom]

theorem mapCoef_mem_center {A B G : Type} [CommSemiring A] [CommSemiring B] [Group G] (f : A →+* B)
    (z : MonoidAlgebra A G) (hz : z ∈ Subalgebra.center A (MonoidAlgebra A G)) :
    mapCoef f z ∈ Subalgebra.center B (MonoidAlgebra B G) := by
  rw [Subalgebra.mem_center_iff] at hz ⊢
  intro b
  rw [mapCoef_eq]
  induction b using MonoidAlgebra.induction_on with
  | of k =>
    have h := congrArg (MonoidAlgebra.mapRingHom G f) (hz (MonoidAlgebra.of A G k))
    rw [map_mul, map_mul] at h
    have hs : MonoidAlgebra.mapRingHom G f (MonoidAlgebra.of A G k) = MonoidAlgebra.of B G k := by
      simp [MonoidAlgebra.of_apply]
    rwa [hs] at h
  | add x y hx hy => rw [add_mul, mul_add, hx, hy]
  | smul r x hx => rw [smul_mul_assoc, mul_smul_comm, hx]

variable {D : D7}

theorem onMt_of_mem (μ : D.what₂.Tup) (j : ℕ) (z : MonoidAlgebra ℂ (G0g D.nd))
    (h : z ∈ Subalgebra.center ℂ (MonoidAlgebra ℂ (G0g D.nd))) :
    D.ntypes.onMt μ j z = D.ntypes.cenMt μ j ⟨z, h⟩ := by
  unfold Formalism.BasicNotions.NTypes.onMt
  rw [dif_pos h]

abbrev CenR (D : D7) (i : D.nd.Loc) : Subalgebra (D.nd.O i) (MonoidAlgebra (D.nd.O i) (G0g D.nd)) :=
  Subalgebra.center (D.nd.O i) (MonoidAlgebra (D.nd.O i) (G0g D.nd))

variable (D) in

def psi (i : D.nd.Loc) (z : MonoidAlgebra (D.nd.O i) (G0g D.nd)) :
    Module.End ℂ (D.what₂.Mt (D.nd.mu i) (D.nd.j i)) :=
  D.ntypes.onMt (D.nd.mu i) (D.nd.j i) (mapCoef (iotaO D.nd D.naut i) z)

theorem psi_mul (i : D.nd.Loc) (a b : MonoidAlgebra (D.nd.O i) (G0g D.nd)) (ha : a ∈ CenR D i)
    (hb : b ∈ CenR D i) : psi D i (a * b) = psi D i a * psi D i b := by
  have ha' := mapCoef_mem_center (iotaO D.nd D.naut i) a ha
  have hb' := mapCoef_mem_center (iotaO D.nd D.naut i) b hb
  unfold psi
  rw [mapCoef_eq, map_mul, ← mapCoef_eq, ← mapCoef_eq, onMt_of_mem _ _ _ (Subalgebra.mul_mem _ ha' hb'),
    onMt_of_mem _ _ _ ha', onMt_of_mem _ _ _ hb', ← map_mul]
  rfl

theorem psi_add (i : D.nd.Loc) (a b : MonoidAlgebra (D.nd.O i) (G0g D.nd)) (ha : a ∈ CenR D i)
    (hb : b ∈ CenR D i) : psi D i (a + b) = psi D i a + psi D i b := by
  have ha' := mapCoef_mem_center (iotaO D.nd D.naut i) a ha
  have hb' := mapCoef_mem_center (iotaO D.nd D.naut i) b hb
  unfold psi
  rw [mapCoef_eq, map_add, ← mapCoef_eq, ← mapCoef_eq, onMt_of_mem _ _ _ (Subalgebra.add_mem _ ha' hb'),
    onMt_of_mem _ _ _ ha', onMt_of_mem _ _ _ hb', ← map_add]
  rfl

theorem psi_smul (i : D.nd.Loc) (c : D.nd.O i) (a : MonoidAlgebra (D.nd.O i) (G0g D.nd)) (ha : a ∈ CenR D i) :
    psi D i (c • a) = iotaO D.nd D.naut i c • psi D i a := by
  have ha' := mapCoef_mem_center (iotaO D.nd D.naut i) a ha
  have hs : mapCoef (iotaO D.nd D.naut i) (c • a) = iotaO D.nd D.naut i c • mapCoef (iotaO D.nd D.naut i) a := by
    rw [mapCoef_eq, mapCoef_eq, Algebra.smul_def, Algebra.smul_def, map_mul]
    congr 1
    simp [MonoidAlgebra.coe_algebraMap, MonoidAlgebra.mapRingHom_single]
  unfold psi
  rw [hs, onMt_of_mem _ _ _ (Subalgebra.smul_mem _ ha' _), onMt_of_mem _ _ _ ha', ← map_smul]
  rfl

theorem psi_one (i : D.nd.Loc) : psi D i 1 = 1 := by
  unfold psi
  rw [mapCoef_eq, map_one, onMt_of_mem _ _ _ (Subalgebra.one_mem _)]
  exact map_one _

theorem psi_zero (i : D.nd.Loc) : psi D i 0 = 0 := by
  unfold psi
  rw [mapCoef_eq, map_zero, onMt_of_mem _ _ _ (Subalgebra.zero_mem _)]
  exact map_zero _

theorem psi_algebraMap (i : D.nd.Loc) (c : D.nd.O i) :
    psi D i (algebraMap (D.nd.O i) (MonoidAlgebra (D.nd.O i) (G0g D.nd)) c) = iotaO D.nd D.naut i c • 1 := by
  rw [Algebra.algebraMap_eq_smul_one, psi_smul i c 1 (Subalgebra.one_mem _), psi_one]

variable {i : D.nd.Loc}

def J (S : Sec D i) (m : D.nd.Mt i) : D.what₂.Mt (D.nd.mu i) (D.nd.j i) :=
  S.Φ ((1 : KK D.nd i) ⊗ₜ[D.nd.O i] m)

theorem J_add (S : Sec D i) (m m' : D.nd.Mt i) : J S (m + m') = J S m + J S m' := by
  simp [J, TensorProduct.tmul_add]

theorem smul_tmul_eq (S : Sec D i) (c : D.nd.O i) (v : TensorProduct (D.nd.O i) (KK D.nd i) (D.nd.Mt i)) :
    S.Φ (c • v) = iotaO D.nd D.naut i c • S.Φ v := by
  rw [← algebraMap_smul (KK D.nd i) c v, S.semi]
  rfl

theorem J_smul (S : Sec D i) (c : D.nd.O i) (m : D.nd.Mt i) : J S (c • m) = iotaO D.nd D.naut i c • J S m := by
  unfold J
  rw [TensorProduct.tmul_smul, smul_tmul_eq]

theorem mk_one_inj : Function.Injective (fun m : D.nd.Mt i => (1 : KK D.nd i) ⊗ₜ[D.nd.O i] m) := by
  have h := Module.Flat.rTensor_preserves_injective_linearMap (M := D.nd.Mt i)
    (Algebra.linearMap (D.nd.O i) (KK D.nd i)) (IsFractionRing.injective (D.nd.O i) (KK D.nd i))
  intro m m' hm
  have e : ∀ m : D.nd.Mt i, (1 : KK D.nd i) ⊗ₜ[D.nd.O i] m =
      LinearMap.rTensor (D.nd.Mt i) (Algebra.linearMap (D.nd.O i) (KK D.nd i)) ((TensorProduct.lid (D.nd.O i) (D.nd.Mt i)).symm m) := by
    intro m
    simp
  dsimp only at hm
  rw [e, e] at hm
  exact (TensorProduct.lid (D.nd.O i) (D.nd.Mt i)).symm.injective (h hm)

theorem J_inj (S : Sec D i) : Function.Injective (J S) := fun _ _ h => mk_one_inj (S.inj h)

section Build

variable (S : Sec D i)
  (hL : ∀ z ∈ CenR D i, ∀ m : D.nd.Mt i, ∃ m' : D.nd.Mt i, J S m' = psi D i z (J S m))

def zL (z : CenR D i) : Module.End (D.nd.O i) (D.nd.Mt i) where
  toFun m := (hL z z.2 m).choose
  map_add' m m' := J_inj S (by
    have h1 := (hL z z.2 (m + m')).choose_spec
    have h2 := (hL z z.2 m).choose_spec
    have h3 := (hL z z.2 m').choose_spec
    rw [h1, J_add S m m', J_add, h2, h3, map_add])
  map_smul' c m := J_inj S (by
    have h1 := (hL z z.2 (c • m)).choose_spec
    have h2 := (hL z z.2 m).choose_spec
    simp only [RingHom.id_apply]
    rw [h1, J_smul S c m, J_smul, h2, map_smul])

theorem zL_spec (z : CenR D i) (m : D.nd.Mt i) : J S (zL S hL z m) = psi D i z (J S m) :=
  (hL z z.2 m).choose_spec

theorem end_ext (A B : Module.End (D.nd.O i) (D.nd.Mt i)) (h : ∀ m, J S (A m) = J S (B m)) : A = B :=
  LinearMap.ext fun m => J_inj S (h m)

def zA : CenR D i →ₐ[D.nd.O i] Module.End (D.nd.O i) (D.nd.Mt i) where
  toFun := zL S hL
  map_one' := end_ext S _ _ fun m => by
    rw [zL_spec]
    change psi D i 1 (J S m) = J S m
    rw [psi_one]; rfl
  map_mul' z z' := end_ext S _ _ fun m => by
    rw [zL_spec, Module.End.mul_apply, zL_spec, zL_spec]
    change psi D i ((z : MonoidAlgebra (D.nd.O i) (G0g D.nd)) * z') (J S m) = _
    rw [psi_mul i _ _ z.2 z'.2]; rfl
  map_zero' := end_ext S _ _ fun m => by
    rw [zL_spec]
    change psi D i 0 (J S m) = J S 0
    rw [psi_zero, LinearMap.zero_apply]
    simp [J]
  map_add' z z' := end_ext S _ _ fun m => by
    rw [zL_spec, LinearMap.add_apply, J_add, zL_spec, zL_spec]
    change psi D i ((z : MonoidAlgebra (D.nd.O i) (G0g D.nd)) + z') (J S m) = _
    rw [psi_add i _ _ z.2 z'.2]; rfl
  commutes' c := end_ext S _ _ fun m => by
    rw [zL_spec]
    change psi D i (algebraMap (D.nd.O i) (MonoidAlgebra (D.nd.O i) (G0g D.nd)) c) (J S m) = _
    rw [psi_algebraMap, Module.algebraMap_end_apply, J_smul]
    rfl

theorem zA_bc (z : CenR D i) (v : TensorProduct (D.nd.O i) (KK D.nd i) (D.nd.Mt i)) :
    S.Φ ((zA S hL z).baseChange (KK D.nd i) v) = psi D i z (S.Φ v) := by
  induction v using TensorProduct.induction_on with
  | zero => simp
  | tmul k m =>
    rw [LinearMap.baseChange_tmul]
    have e : ∀ n : D.nd.Mt i, k ⊗ₜ[D.nd.O i] n = k • ((1 : KK D.nd i) ⊗ₜ[D.nd.O i] n) := fun n => by
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rw [e, e, S.semi, S.semi, map_smul]
    congr 1
    exact zL_spec S hL z m
  | add v w hv hw => rw [map_add, map_add, hv, hw, map_add, map_add]

end Build

section Laws

variable (S : Sec D i)
  (hL : ∀ z ∈ CenR D i, ∀ m : D.nd.Mt i, ∃ m' : D.nd.Mt i, J S m' = psi D i z (J S m))

theorem zA_comm (h4 : ∀ (c : MonoidAlgebra ℂ (G0g D.nd)) (x : D.nd.X i)
      (u w : TensorProduct (D.nd.O i) (KK D.nd i) (D.nd.Mt i)), u ∈ heckeEig (D.nd.T i) (D.nd.act i) x →
      S.Φ w = D.ntypes.onMt (D.nd.mu i) (D.nd.j i) c (S.Φ u) → w ∈ heckeEig (D.nd.T i) (D.nd.act i) x)
    (z : CenR D i) (f : D.nd.T i) : zA S hL z * D.nd.act i f = D.nd.act i f * zA S hL z := by
  have key : ∀ v, (zA S hL z).baseChange (KK D.nd i) ((D.nd.act i f).baseChange (KK D.nd i) v) =
      (D.nd.act i f).baseChange (KK D.nd i) ((zA S hL z).baseChange (KK D.nd i) v) := by
    intro v
    have hv : v ∈ (⨆ x, heckeEig (D.nd.T i) (D.nd.act i) x) := by
      rw [Formalism.MainNotions.TruncatedSeriesCountingIdentities.Br.EigSpan_holds D.nd i]; trivial
    refine Submodule.iSup_induction _ (motive := fun v => (zA S hL z).baseChange (KK D.nd i)
      ((D.nd.act i f).baseChange (KK D.nd i) v) = (D.nd.act i f).baseChange (KK D.nd i)
      ((zA S hL z).baseChange (KK D.nd i) v)) hv ?_ ?_ ?_
    · intro x u hu
      have hw := h4 _ x u _ hu (zA_bc S hL z u)
      have e1 := (Submodule.mem_iInf _).1 hu f
      have e2 := (Submodule.mem_iInf _).1 hw f
      rw [Module.End.mem_eigenspace_iff] at e1 e2
      rw [e1, e2, map_smul]
    · simp
    · intro v w hv hw
      rw [map_add, map_add, hv, hw, map_add, map_add]
  apply end_ext S
  intro m
  simp only [Module.End.mul_apply]
  unfold J
  have e : ∀ (A : Module.End (D.nd.O i) (D.nd.Mt i)) (n : D.nd.Mt i),
      (1 : KK D.nd i) ⊗ₜ[D.nd.O i] A n = A.baseChange (KK D.nd i) ((1 : KK D.nd i) ⊗ₜ[D.nd.O i] n) :=
    fun A n => by rw [LinearMap.baseChange_tmul]
  rw [e, e (D.nd.act i f) m, e (D.nd.act i f), e (zA S hL z) m, key]

theorem zA_act (h1 : ∀ (c : MonoidAlgebra ℂ (G0g D.nd)) (x y : D.what₂.MtL (D.nd.mu i) (D.nd.j i)),
      D.what₂.jMt _ _ y = D.ntypes.onMt (D.nd.mu i) (D.nd.j i) c (D.what₂.jMt _ _ x) →
      S.Φ (D.nd.prMt i y) = D.ntypes.onMt (D.nd.mu i) (D.nd.j i) c (S.Φ (D.nd.prMt i x)))
    (z : CenR D i) (x y : D.what₂.MtL (D.nd.mu i) (D.nd.j i))
    (hxy : D.what₂.jMt _ _ y = D.ntypes.onMt (D.nd.mu i) (D.nd.j i)
      (mapCoef (iotaO D.nd D.naut i) (z : MonoidAlgebra (D.nd.O i) (G0g D.nd))) (D.what₂.jMt _ _ x)) :
    D.nd.prMt i y = (zA S hL z).baseChange (KK D.nd i) (D.nd.prMt i x) :=
  S.inj (by rw [h1 _ x y hxy, zA_bc]; rfl)

end Laws

theorem hL_of (S : Sec D i)
    (hlat : ∀ (c : MonoidAlgebra ℤ (G0g D.nd)), (∀ a, c * a = a * c) → ∀ m : D.nd.Mt i, ∃ m' : D.nd.Mt i,
      J S m' = D.ntypes.onMt (D.nd.mu i) (D.nd.j i) (mapCoef (Int.castRingHom ℂ) c) (J S m))
    (hcls : ∀ z ∈ CenR D i, z ∈ Submodule.span (D.nd.O i)
      ((MonoidAlgebra.mapRingHom (G0g D.nd) (Int.castRingHom (D.nd.O i))) ''
        {c : MonoidAlgebra ℤ (G0g D.nd) | ∀ a, c * a = a * c})) :
    ∀ z ∈ CenR D i, ∀ m : D.nd.Mt i, ∃ m' : D.nd.Mt i, J S m' = psi D i z (J S m) := by
  intro z hz
  refine (Submodule.span_induction (p := fun z _ => z ∈ CenR D i ∧
    ∀ m : D.nd.Mt i, ∃ m' : D.nd.Mt i, J S m' = psi D i z (J S m)) ?_ ?_ ?_ ?_ (hcls z hz)).2
  · rintro _ ⟨c, hc, rfl⟩
    have hc' : c ∈ Subalgebra.center ℤ (MonoidAlgebra ℤ (G0g D.nd)) :=
      Subalgebra.mem_center_iff.2 fun b => (hc b).symm
    refine ⟨?_, fun m => ?_⟩
    · rw [← mapCoef_eq]; exact mapCoef_mem_center _ c hc'
    · obtain ⟨m', hm'⟩ := hlat c hc m
      refine ⟨m', ?_⟩
      rw [hm']
      have e : mapCoef (iotaO D.nd D.naut i) (MonoidAlgebra.mapRingHom (G0g D.nd) (Int.castRingHom (D.nd.O i)) c) =
          mapCoef (Int.castRingHom ℂ) c := by
        rw [mapCoef_eq, mapCoef_eq, ← RingHom.comp_apply, ← MonoidAlgebra.mapRingHom_comp]
        congr 2
        exact Subsingleton.elim _ _
      unfold psi
      rw [e]
  · refine ⟨Subalgebra.zero_mem _, fun m => ⟨0, ?_⟩⟩
    rw [psi_zero, LinearMap.zero_apply]
    simp [J]
  · rintro a b _ _ ⟨ha, fa⟩ ⟨hb, fb⟩
    refine ⟨Subalgebra.add_mem _ ha hb, fun m => ?_⟩
    obtain ⟨ma, hma⟩ := fa m
    obtain ⟨mb, hmb⟩ := fb m
    exact ⟨ma + mb, by rw [J_add, hma, hmb, psi_add i a b ha hb, LinearMap.add_apply]⟩
  · rintro r a _ ⟨ha, fa⟩
    refine ⟨Subalgebra.smul_mem _ ha r, fun m => ?_⟩
    obtain ⟨ma, hma⟩ := fa m
    exact ⟨r • ma, by rw [J_smul, hma, psi_smul i r a ha, LinearMap.smul_apply]⟩

end GlobalTheory.CenOAct

namespace GlobalTheory.CenOAct

theorem cenO_nonempty : ∀ D : D7, (∀ i, Nonempty (Sec D i)) → ZLStable D → CenInt D → OnMtPreservesTypeV D → Nonempty (CenO D) := by
  intro D hS _ hInt hTy
  haveI : ∀ k : Fin 2, NeZero (D.host.g k) := fun k => ⟨(D.host.g_prime k).ne_zero⟩
  haveI : Finite (G0g D.nd) := inferInstance
  have S : ∀ i, Sec D i := fun i => (hS i).some
  have hint : ∀ (i : D.nd.Loc) (a : 𝓞 D.what₂.LL), D.nd.embK i (a : D.what₂.LL) ∈
      (algebraMap (D.nd.O i) (FractionRing (D.nd.O i))).range := fun i a =>
    (D.nd.embK_w i a).1 (GlobalTheory.T.addValuation_nonneg_ringOfIntegers_numberField D.what₂.LL (D.what₂.places.val (D.nd.w i)) a)
  have hL : ∀ i, ∀ z ∈ CenR D i, ∀ m : D.nd.Mt i, ∃ m' : D.nd.Mt i, J (S i) m' = psi D i z (J (S i) m) :=
    fun i => hL_of (S i) (GlobalTheory.T.centralIntegral_preserves_localisedLatticeImage D i (S i) (hint i) (GlobalTheory.T.comparisonMap_intertwines_groupAlgebra_action D i (S i) hTy) hInt)
      (fun z hz => GlobalTheory.T.center_monoidAlgebra_le_span_centralIntegral (D.nd.O i) (G0g D.nd) z hz)
  exact ⟨{ zO := fun i => zA (S i) (hL i)
           zO_comm := fun i z f => zA_comm (S i) (hL i) (GlobalTheory.T.mem_heckeEig_of_image_moved_by_centre D i (S i) hTy) z f
           zO_act := fun i z x y h => zA_act (S i) (hL i) (GlobalTheory.T.comparisonMap_intertwines_groupAlgebra_action D i (S i) hTy) z x y h }⟩

end GlobalTheory.CenOAct

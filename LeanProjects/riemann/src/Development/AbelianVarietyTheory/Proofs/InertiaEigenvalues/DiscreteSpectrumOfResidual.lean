import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DiscreteSpectrumResidual
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HasInfCharInfCharOfCommute
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CapCommuteRtInfGL
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CommuteCapOfCommuteEop
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeCharExponentOfInfinityType
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CapelliDetBlockLeviCongrModUpperBlockIdealStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UpperMatrixUnitKillsUnipotentInvariantOnLeviStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CapelliDetDiagonalBlockActsByInfinitesimalCharacStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdelicGLIwasawaDecompositionStandardParabolicStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LieMemCompactFiniteVectorsOfMemStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LieDerivativeInducedTensorFormsStatement

noncomputable section

open NumberField IsDedekindDomain Formalism.L2.Host
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec

namespace GlobalTheory.SpehInfChar

theorem lie_mem_finVec : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] {N : ℕ} (X : Lie E N)
    (φ : Sm E N), φ ∈ finVec (cptRep E N) → lie E N X φ ∈ finVec (cptRep E N) :=
  GlobalTheory.T.lie_mem_compactFiniteVectors_of_mem

theorem lie_tensorForms : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] {c N : ℕ} (n : Fin c → ℕ)
    (h : ∑ i, n i = N) (π : ∀ i, CuspSub E (n i)) (X : Lie E N) (φ : Sm E N), φ ∈ indForms h π →
    ∀ (k : Kinf E N) (g : GL (Fin N) (Af E)), (fun m => (lie E N X φ).1 (leviEmb (Ad E) (stdBlocks n h) m *
      (infGL E N (Unitary.toUnits k) * finGL E N g))) ∈ tensorForms π :=
  GlobalTheory.T.lie_derivative_induced_tensor_forms

theorem qdet_sub_blocks_mem : ∀ (A : Type) [Ring A] [Algebra ℂ A] {c N : ℕ} (n : Fin c → ℕ) (h : ∑ i, n i = N)
    (X : Fin N → Fin N → A), Formalism.REAL.GlRel X → ∀ u : ℂ,
    Formalism.REAL.qdet X (u + ((N : ℂ) - 1) / 2) -
              (List.ofFn fun i : Fin c => Formalism.REAL.qdet (fun p q : Fin (n i) => X (stdBlocks n h ⟨i, p⟩) (stdBlocks n h ⟨i, q⟩))
                (u + ((n i : ℂ) - 1) / 2 - (modExp (fun i => Fin (n i)) i : ℂ) / 2)).prod ∈
      Submodule.span ℂ {y : A | ∃ (p q : Fin N) (w : A), blk (stdBlocks n h) p < blk (stdBlocks n h) q ∧ y = X p q * w} :=
  GlobalTheory.T.capelliDet_block_levi_congr_mod_upperBlockIdeal

theorem Eop_leviEmb_eq_zero : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] {c N : ℕ} (n : Fin c → ℕ)
    (h : ∑ i, n i = N) (ψ : Sm E N), (∀ u ∈ unipRad (Ad E) (stdBlocks n h), ∀ g, ψ.1 (u * g) = ψ.1 g) →
    ∀ (τ : E →+* ℂ) (p q : Fin N), blk (stdBlocks n h) p < blk (stdBlocks n h) q →
    ∀ m, (Eop τ p q ψ).1 (leviEmb (Ad E) (stdBlocks n h) m) = 0 :=
  GlobalTheory.T.upperMatrixUnit_kills_unipotentInvariant_on_levi

theorem blockCap_leviEmb : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] {c N : ℕ} (n : Fin c → ℕ)
    (h : ∑ i, n i = N) (π : ∀ i, CuspSub E (n i)) (τ : E →+* ℂ) (i : Fin c) (M : Multiset ℂ), (π i).HasInfChar τ M →
    ∀ (u : ℂ) (ψ : Sm E N), (fun m => ψ.1 (leviEmb (Ad E) (stdBlocks n h) m)) ∈ tensorForms π →
    ∀ m, (Formalism.REAL.qdet (fun p q : Fin (n i) => Eop (a := N) τ (stdBlocks n h ⟨i, p⟩) (stdBlocks n h ⟨i, q⟩))
      (u + ((n i : ℂ) - 1) / 2) ψ).1 (leviEmb (Ad E) (stdBlocks n h) m) =
      (M.map (u + ·)).prod * ψ.1 (leviEmb (Ad E) (stdBlocks n h) m) :=
  GlobalTheory.T.capelliDet_diagonalBlock_acts_by_infinitesimalCharacter

theorem exists_iwasawa : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] {c N : ℕ} (n : Fin c → ℕ)
    (h : ∑ i, n i = N) (x : GA E N), ∃ u ∈ unipRad (Ad E) (stdBlocks n h), ∃ (m : ∀ i, GA E (n i)) (k : Kinf E N)
      (g : GL (Fin N) (Af E)), x = u * leviEmb (Ad E) (stdBlocks n h) m * (infGL E N (Unitary.toUnits k) * finGL E N g) :=
  GlobalTheory.T.adelicGL_iwasawa_decomposition_standardParabolic

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E]

theorem lie_leftInv {N : ℕ} (U : Subgroup (GA E N)) (X : Lie E N) {ψ : Sm E N}
    (hψ : ∀ u ∈ U, ∀ g, ψ.1 (u * g) = ψ.1 g) : ∀ u ∈ U, ∀ g, (lie E N X ψ).1 (u * g) = (lie E N X ψ).1 g := by
  intro u hu g
  have e : chart ψ.1 (u * g) = chart ψ.1 g := by
    funext x
    unfold chart
    split_ifs with hx
    · rw [mul_assoc, hψ u hu]
    · rfl
  simp only [lie_apply, lieD, e]

def leftInvAlg {N : ℕ} (U : Subgroup (GA E N)) : Subalgebra ℂ (Module.End ℂ (Sm E N)) where
  carrier := {z | ∀ ψ : Sm E N, (∀ u ∈ U, ∀ g, ψ.1 (u * g) = ψ.1 g) → ∀ u ∈ U, ∀ g, (z ψ).1 (u * g) = (z ψ).1 g}
  mul_mem' hx hy ψ hψ := hx _ (hy ψ hψ)
  add_mem' {x y} hx hy ψ hψ u hu g := by
    change (x ψ).1 (u * g) + (y ψ).1 (u * g) = (x ψ).1 g + (y ψ).1 g
    rw [hx ψ hψ u hu g, hy ψ hψ u hu g]
  algebraMap_mem' c ψ hψ u hu g := by
    simp only [Module.algebraMap_end_apply, Submodule.coe_smul, Pi.smul_apply, hψ u hu g]

theorem Eop_mem_leftInvAlg {N : ℕ} (U : Subgroup (GA E N)) (τ : E →+* ℂ) (p q : Fin N) : Eop τ p q ∈ leftInvAlg U := by
  have hL : ∀ X, lie E N X ∈ leftInvAlg U := fun X ψ hψ => lie_leftInv U X hψ
  exact Subalgebra.smul_mem _ (Subalgebra.sub_mem _ (hL _) (Subalgebra.smul_mem _ (hL _) _)) _

theorem cap_comm_quot {N : ℕ} {I : Submodule ℂ (Sm E N)} (hI : ∀ X, ∀ φ ∈ I, lie E N X φ ∈ I)
    (f : Sm E N →ₗ[ℂ] Sm E N) (hf : ∀ o, ∀ φ ∈ I, f (act o φ) = act o (f φ)) (τ : E →+* ℂ) (u : ℂ) :
    ∀ φ ∈ I, f (cap τ u φ) = cap τ u (f φ) := by
  let S : Subalgebra ℂ (Module.End ℂ (Sm E N)) :=
    { carrier := {z | ∀ φ ∈ I, z φ ∈ I ∧ f (z φ) = z (f φ)}
      mul_mem' := fun {x y} hx hy φ hφ => by
        obtain ⟨h1, e1⟩ := hy φ hφ
        obtain ⟨h2, e2⟩ := hx _ h1
        exact ⟨h2, by simp only [Module.End.mul_apply]; rw [e2, e1]⟩
      add_mem' := fun {x y} hx hy φ hφ => by
        obtain ⟨h1, e1⟩ := hx φ hφ
        obtain ⟨h2, e2⟩ := hy φ hφ
        exact ⟨add_mem h1 h2, by simp only [LinearMap.add_apply, map_add, e1, e2]⟩
      algebraMap_mem' := fun c φ hφ => ⟨by simpa only [Module.algebraMap_end_apply] using I.smul_mem c hφ,
        by simp only [Module.algebraMap_end_apply, map_smul]⟩ }
  have hL : ∀ X, lie E N X ∈ S := fun X φ hφ => ⟨hI X φ hφ, hf (.lie X) φ hφ⟩
  have hE : ∀ i j, Eop τ i j ∈ S := fun i j => S.smul_mem (S.sub_mem (hL _) (S.smul_mem (hL _) _)) _
  have : cap τ u ∈ S := by
    refine S.sum_mem fun σ _ => S.mul_mem (intCast_mem S _) (S.list_prod_mem fun x hx => ?_)
    obtain ⟨k, rfl⟩ := List.mem_ofFn.1 hx
    refine S.add_mem ?_ (hE _ _)
    split_ifs
    · exact S.algebraMap_mem _
    · exact S.zero_mem
  exact fun φ hφ => (this φ hφ).2

theorem list_prod_along {ι : Type} {N : ℕ} (ℓ : ι → GA E N) (T : Submodule ℂ (ι → ℂ))
    (l : List (Module.End ℂ (Sm E N) × ℂ))
    (hl : ∀ x ∈ l, ∀ ψ : Sm E N, (fun m => ψ.1 (ℓ m)) ∈ T → ∀ m, (x.1 ψ).1 (ℓ m) = x.2 * ψ.1 (ℓ m)) :
    ∀ ψ : Sm E N, (fun m => ψ.1 (ℓ m)) ∈ T → ∀ m,
      ((l.map Prod.fst).prod ψ).1 (ℓ m) = (l.map Prod.snd).prod * ψ.1 (ℓ m) := by
  induction l with
  | nil => intro ψ _ m; simp
  | cons x l ih =>
    intro ψ hψ m
    have ih' := ih fun y hy => hl y (List.mem_cons_of_mem _ hy)
    have h2 : (fun m => ((l.map Prod.fst).prod ψ).1 (ℓ m)) ∈ T := by
      have : (fun m => ((l.map Prod.fst).prod ψ).1 (ℓ m)) = (l.map Prod.snd).prod • (fun m => ψ.1 (ℓ m)) :=
        funext fun m => by rw [ih' ψ hψ m]; rfl
      rw [this]
      exact T.smul_mem _ hψ
    simp only [List.map_cons, List.prod_cons, Module.End.mul_apply]
    rw [hl x (by simp) _ h2 m, ih' ψ hψ m, mul_assoc]

theorem lie_mem_smoothPart {N : ℕ} (X : Lie E N) {φ : Sm E N} (hφ : φ ∈ GlobalTheory.PRep.smoothPart (finRep E N)) :
    lie E N X φ ∈ GlobalTheory.PRep.smoothPart (finRep E N) := by
  have ho : IsOpen {k | finRep E N k φ = φ} := hφ
  refine isOpen_stab_of_mem_nhds _ _ (Filter.mem_of_superset (ho.mem_nhds (by simp)) fun k hk => ?_)
  have hk' : finRep E N k φ = φ := hk
  change finRep E N k (lie E N X φ) = lie E N X φ
  have e := congrArg (fun z => z φ) (lie_rt_fin X k)
  simp only [Module.End.mul_apply] at e
  change lie E N X (finRep E N k φ) = finRep E N k (lie E N X φ) at e
  rw [← e, hk']

theorem lie_mem_indForms {c N : ℕ} (n : Fin c → ℕ) (h : ∑ i, n i = N) (π : ∀ i, CuspSub E (n i)) (X : Lie E N)
    (φ : Sm E N) (hφ : φ ∈ indForms h π) : lie E N X φ ∈ indForms h π :=
  ⟨lie_leftInv _ X hφ.1, lie_mem_smoothPart X hφ.2.1, lie_mem_finVec E X φ hφ.2.2.1,
    lie_tensorForms E n h π X φ hφ⟩

theorem cap_indForms {c N : ℕ} (n : Fin c → ℕ) (h : ∑ i, n i = N) (π : ∀ i, CuspSub E (n i)) (τ : E →+* ℂ)
    (M : Fin c → Multiset ℂ) (hM : ∀ i, (π i).HasInfChar τ (M i)) (u : ℂ) (φ : Sm E N) (hφ : φ ∈ indForms h π) :
    cap τ u φ = (∏ i, ((M i).map fun x => u + x - (modExp (fun i => Fin (n i)) i : ℂ) / 2).prod) • φ := by
  set e := stdBlocks n h with he
  set mE : Fin c → ℂ := fun i => (modExp (fun i => Fin (n i)) i : ℂ) / 2 with hmE
  let S : Subalgebra ℂ (Module.End ℂ (Sm E N)) :=
    Algebra.adjoin ℂ (Set.range fun pq : Fin N × Fin N => Eop τ pq.1 pq.2)
  have hSE : ∀ p q, Eop τ p q ∈ S := fun p q => Algebra.subset_adjoin ⟨(p, q), rfl⟩
  have hSL : S ≤ leftInvAlg (unipRad (Ad E) e) :=
    Algebra.adjoin_le (by rintro _ ⟨pq, rfl⟩; exact Eop_mem_leftInvAlg _ τ pq.1 pq.2)
  let X : Fin N → Fin N → S := fun p q => ⟨Eop τ p q, hSE p q⟩
  have hX : Formalism.REAL.GlRel X := fun a b c' d => Subtype.ext (by
    have := glRel_Eop (a := N) τ a b c' d
    split_ifs at this ⊢ <;> simpa [X] using this)
  have key := qdet_sub_blocks_mem S n h X hX u

  let B : Fin c → Module.End ℂ (Sm E N) := fun i =>
    Formalism.REAL.qdet (fun p q : Fin (n i) => Eop (a := N) τ (e ⟨i, p⟩) (e ⟨i, q⟩)) (u + ((n i : ℂ) - 1) / 2 - mE i)
  let sc : Fin c → ℂ := fun i => ((M i).map fun x => u + x - mE i).prod
  have hval : S.val (List.ofFn fun i : Fin c => Formalism.REAL.qdet (fun p q : Fin (n i) => X (e ⟨i, p⟩) (e ⟨i, q⟩))
      (u + ((n i : ℂ) - 1) / 2 - mE i)).prod = (List.ofFn B).prod := by
    rw [map_list_prod, List.map_ofFn]
    congr 1
    refine List.ofFn_inj.2 (funext fun i => ?_)
    simp only [Function.comp_apply, B]
    rw [map_qdet]
    rfl
  have hcap : S.val (Formalism.REAL.qdet X (u + ((N : ℂ) - 1) / 2)) = cap τ u := by
    rw [map_qdet]
    rfl

  have hlevi : ∀ ψ : Sm E N, (∀ v ∈ unipRad (Ad E) e, ∀ g, ψ.1 (v * g) = ψ.1 g) →
      (fun m => ψ.1 (leviEmb (Ad E) e m)) ∈ tensorForms π → ∀ m,
      (cap τ u ψ).1 (leviEmb (Ad E) e m) = (∏ i, sc i) * ψ.1 (leviEmb (Ad E) e m) := by
    intro ψ hψ hT m
    let L : S →ₗ[ℂ] ℂ :=
      { toFun := fun w => ((w : Module.End ℂ (Sm E N)) ψ).1 (leviEmb (Ad E) e m)
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl }
    have hker : Submodule.span ℂ {y : S | ∃ (p q : Fin N) (w : S), blk e p < blk e q ∧ y = X p q * w} ≤
        LinearMap.ker L := by
      refine Submodule.span_le.2 ?_
      rintro _ ⟨p, q, w, hpq, rfl⟩
      change (Eop τ p q ((w : Module.End ℂ (Sm E N)) ψ)).1 (leviEmb (Ad E) e m) = 0
      exact Eop_leviEmb_eq_zero E n h _ (hSL w.2 ψ hψ) τ p q hpq m
    have h1 := hker key
    rw [LinearMap.mem_ker, map_sub, sub_eq_zero] at h1
    change ((S.val (Formalism.REAL.qdet X _)) ψ).1 _ = ((S.val _) ψ).1 _ at h1
    rw [hcap, hval] at h1
    rw [h1]
    have hl := list_prod_along (leviEmb (Ad E) e) (tensorForms π) (List.ofFn fun i => (B i, sc i)) (by
      intro x hx ψ' hψ' m'
      obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hx
      have := blockCap_leviEmb E n h π τ i (M i) (hM i) (u - mE i) ψ' hψ' m'
      have e1 : u - mE i + ((n i : ℂ) - 1) / 2 = u + ((n i : ℂ) - 1) / 2 - mE i := by ring
      have e2 : ((M i).map (u - mE i + ·)) = (M i).map fun x => u + x - mE i :=
        Multiset.map_congr rfl fun x _ => by ring
      rw [e1, e2] at this
      exact this) ψ hT m
    simp only [List.map_ofFn] at hl
    rw [List.prod_ofFn] at hl
    exact hl
  refine Subtype.ext (funext fun x => ?_)
  obtain ⟨v, hv, m, k, g, rfl⟩ := exists_iwasawa E n h x
  set y := infGL E N (Unitary.toUnits k) * finGL E N g
  have hcapInv : ∀ v ∈ unipRad (Ad E) e, ∀ g, (cap τ u φ).1 (v * g) = (cap τ u φ).1 g := by
    have : cap τ u ∈ S := by
      rw [← hcap]; exact (Formalism.REAL.qdet X _).2
    exact hSL this φ hφ.1
  have hcomm : Commute (cap τ u) (rt E N y) := by
    rw [map_mul]
    exact (GlobalTheory.CapAdInv.cap_commute_rt_infGL E N τ u _).mul_right (commute_cap_finRep τ u g)
  set ψ := rt E N y φ
  have hψ : ∀ v ∈ unipRad (Ad E) e, ∀ g, ψ.1 (v * g) = ψ.1 g := fun v hv g => by
    simp only [ψ, rt_apply, mul_assoc]
    exact hφ.1 v hv _
  have hψT : (fun m => ψ.1 (leviEmb (Ad E) e m)) ∈ tensorForms π := hφ.2.2.2 k g
  have h3 := hlevi ψ hψ hψT m
  have h4 : (cap τ u ψ).1 (leviEmb (Ad E) e m) = (cap τ u φ).1 (leviEmb (Ad E) e m * y) := by
    rw [← rt_apply, ← Module.End.mul_apply, hcomm.eq]
    rfl
  rw [mul_assoc, hcapInv v hv, ← h4, h3]
  simp only [Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, ψ, rt_apply]
  rw [hφ.1 v hv]

theorem prod_map_finset_sum {ι : Type} (s : Finset ι) (A : ι → Multiset ℂ) (g : ℂ → ℂ) :
    ((∑ j ∈ s, A j).map g).prod = ∏ j ∈ s, ((A j).map g).prod := by
  classical
  refine Finset.induction_on s (by simp) fun j s hj ih => ?_
  rw [Finset.sum_insert hj, Finset.prod_insert hj, Multiset.map_add, Multiset.prod_add, ih]

theorem cap_commute_act {a : ℕ} (τ : E →+* ℂ) (u : ℂ) (o : Op E a) : Commute (cap (a := a) τ u) (act o) := by
  cases o with
  | fin k => exact commute_cap_finRep τ u k
  | cpt k => exact GlobalTheory.CapAdInv.cap_commute_rt_infGL E a τ u _
  | lie X => exact commute_cap_lie τ u X

theorem hasInfCharGL_of_isSpehOf {N a d : ℕ} {V : Submodule ℂ (Sm E N)} {π : CuspSub E a} (hV : IsSpehOf V π d)
    (τ : E →+* ℂ) : ∃ m, π.HasInfChar τ m ∧ HasInfCharGL V τ (GlobalTheory.SphGal.spehInf d m) := by
  have hm : π.HasInfChar τ ((CG.mk π).infChar τ) :=
    hasInfChar_infChar_of_commute E a (fun τ u o => cap_commute_act τ u o) (CG.mk π) τ
  refine ⟨(CG.mk π).infChar τ, hm, ?_, fun u ψ hψ => ?_⟩
  · have hN := hV.mul_eq
    simp only [GlobalTheory.SphGal.spehInf, Multiset.card_sum, Multiset.card_map, hm.1, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, smul_eq_mul]
    exact hN
  obtain ⟨hs, ν, hν, f, hfV, hf⟩ := hV
  set m := (CG.mk π).infChar τ
  have hI : ∀ X, ∀ φ ∈ indForms hs (fun i => π.twist (ν i)), lie E N X φ ∈ indForms hs (fun i => π.twist (ν i)) :=
    fun X φ hφ => lie_mem_indForms _ hs _ X φ hφ
  rw [← hfV] at hψ
  obtain ⟨φ, hφ, rfl⟩ := hψ
  have hexpo : ∀ i : Fin d, expo (ν i) τ = ((spehExp d i + a * spehExp d i : ℝ) : ℂ) := fun i =>
    (GlobalTheory.CuspRep.InfType.expo_of_infType E (ν i)).2.1 _ (hν i) τ
  have hmod : ∀ i : Fin d, ((modExp (fun _ : Fin d => Fin a) i : ℤ) : ℂ) / 2 = ((a * spehExp d i : ℝ) : ℂ) := fun i => by
    rw [mul_spehExp]
    push_cast
    rfl
  have hc := cap_indForms (fun _ : Fin d => a) hs (fun i => π.twist (ν i)) τ (fun i => m.map (· + expo (ν i) τ))
    (fun i => hm.twist (ν i)) u φ hφ
  rw [cap_comm_quot hI f hf τ u φ hφ |>.symm, hc, map_smul]
  congr 1
  rw [GlobalTheory.SphGal.spehInf, prod_map_finset_sum]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [Multiset.map_map, Multiset.map_map]
  congr 1
  refine Multiset.map_congr rfl fun x _ => ?_
  simp only [Function.comp_apply]
  have h1 := hexpo i
  have h2 := hmod i
  have h3 : ((spehExp d i : ℝ) : ℂ) = ((d : ℂ) - 1) / 2 - ((i : ℕ) : ℂ) := by
    simp [spehExp]
  change u + (x + expo (ν i) τ) - ((modExp (fun _ : Fin d => Fin a) i : ℤ) : ℂ) / 2 = u + (x + (((d : ℂ) - 1) / 2 - ((i : ℕ) : ℂ)))
  rw [h1, h2, ← h3]
  push_cast
  ring

theorem discreteSpectrumGL_of_residual : GlobalTheory.Published.DiscreteSpectrumResidual → GlobalTheory.Published.DiscreteSpectrumGL := by
  intro H E _ _ _ N hN
  obtain ⟨h1, h2, h3, h4, h5⟩ := H E N hN
  exact ⟨h1, h2, h3, h4, fun V hV a d π hn e => ⟨fun w => (h5 V hV a d π hn e w).1, fun w => (h5 V hV a d π hn e w).2,
    hasInfCharGL_of_isSpehOf e⟩⟩

end GlobalTheory.SpehInfChar

import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.EntryMem
import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.WcompMulHomog
import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.SInternal

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement

private theorem pt_of_ft {K C : Type} [Field K] [IsAlgClosed K] [CommRing C] [Algebra K C] [Nontrivial C]
    [Algebra.FiniteType K C] : Nonempty (C →ₐ[K] K) := by
  obtain ⟨m, hm⟩ := Ideal.exists_maximal C
  letI : Field (C ⧸ m) := Ideal.Quotient.field m
  haveI : Algebra.FiniteType K (C ⧸ m) :=
    Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ K m) (Ideal.Quotient.mkₐ_surjective K m)
  haveI : Module.Finite K (C ⧸ m) := finite_of_finite_type_of_isJacobsonRing K (C ⧸ m)
  haveI : Algebra.IsIntegral K (C ⧸ m) := Algebra.IsIntegral.of_finite K _
  have hb : Function.Bijective (algebraMap K (C ⧸ m)) := IsAlgClosed.algebraMap_bijective_of_isIntegral
  exact ⟨((AlgEquiv.ofBijective (Algebra.ofId K (C ⧸ m)) hb).symm : (C ⧸ m) →ₐ[K] K).comp
    (Ideal.Quotient.mkₐ K m)⟩

private theorem pt_of_lin {A B K : Type} [CommRing A] [CommRing B] [Field K] [IsAlgClosed K] [Algebra A B]
    [Algebra A K] [Algebra.FiniteType A B] (ρ : B →ₗ[A] K) (h : ρ 1 = 1) : Nonempty (B →ₐ[A] K) := by
  classical
  let f : TensorProduct A K B →ₗ[A] K := TensorProduct.lift ((LinearMap.mul A K).compl₂ ρ)
  have hf : f 1 = 1 := by
    rw [Algebra.TensorProduct.one_def]
    simp [f, h]
  haveI : Nontrivial (TensorProduct A K B) := by
    refine ⟨⟨1, 0, fun h0 => ?_⟩⟩
    have h1 := congrArg f h0
    rw [hf, map_zero] at h1
    exact one_ne_zero h1
  haveI : Algebra.FiniteType K (TensorProduct A K B) := Algebra.FiniteType.baseChange K
  obtain ⟨φ⟩ := pt_of_ft (K := K) (C := TensorProduct A K B)
  exact ⟨(φ.restrictScalars A).comp Algebra.TensorProduct.includeRight⟩

private theorem ext_of_proj {O A B K : Type} [CommRing O] [CommRing A] [CommRing B] [Field K] [IsAlgClosed K]
    [Algebra O A] [Algebra O B] [Algebra O K] (φ : A →ₐ[O] B) (x : A →ₐ[O] K) (hk : ∀ f, φ f = 0 → x f = 0)
    (P : B →+ B) (hP : ∀ f s, P (φ f * s) = φ f * P s) (hr : ∀ s, ∃ f, φ f = P s) (h1 : P 1 = 1)
    (s : Set B) (hs : s.Finite) (hg : Algebra.adjoin O (Set.range φ ∪ s) = ⊤) :
    ∃ ξ : B →ₐ[O] K, ξ.comp φ = x := by
  classical
  letI : Algebra A B := φ.toRingHom.toAlgebra
  letI : Algebra A K := x.toRingHom.toAlgebra
  have hwd : ∀ f g, φ f = φ g → x f = x g := fun f g hfg => by
    have h0 := hk (f - g) (by rw [map_sub, hfg, sub_self])
    rwa [map_sub, sub_eq_zero] at h0
  choose pre hpre using hr
  have hO : ∀ r : O, algebraMap O B r = algebraMap A B (algebraMap O A r) := fun r => by
    show algebraMap O B r = φ (algebraMap O A r)
    rw [AlgHom.commutes]
  let ρ : B →ₗ[A] K :=
    { toFun := fun t => x (pre t)
      map_add' := fun t u => by
        rw [← map_add]
        apply hwd
        rw [map_add, hpre, hpre, hpre, map_add]
      map_smul' := fun a t => by
        show x (pre (a • t)) = x a * x (pre t)
        rw [← map_mul]
        apply hwd
        rw [hpre, map_mul, hpre, Algebra.smul_def]
        exact hP a t }
  have h1' : ρ 1 = 1 := by
    show x (pre 1) = 1
    rw [← map_one x]
    apply hwd
    rw [hpre, h1, map_one]
  haveI : Algebra.FiniteType A B := by
    refine ⟨⟨hs.toFinset, ?_⟩⟩
    rw [eq_top_iff]
    rintro b -
    have hb : b ∈ Algebra.adjoin O (Set.range φ ∪ s) := by
      rw [hg]
      trivial
    rw [Set.Finite.coe_toFinset]
    induction hb using Algebra.adjoin_induction with
    | mem y hy =>
      rcases hy with ⟨f, rfl⟩ | hy
      · exact Subalgebra.algebraMap_mem _ f
      · exact Algebra.subset_adjoin hy
    | algebraMap r =>
      rw [hO]
      exact Subalgebra.algebraMap_mem _ _
    | add y z _ _ hy hz => exact add_mem hy hz
    | mul y z _ _ hy hz => exact mul_mem hy hz
  obtain ⟨ψ⟩ := pt_of_lin ρ h1'
  refine ⟨{ toRingHom := ψ.toRingHom, commutes' := fun r => ?_ }, ?_⟩
  · show ψ (algebraMap O B r) = algebraMap O K r
    rw [hO, ψ.commutes]
    exact x.commutes r
  · ext f
    exact ψ.commutes f

private theorem exists_proj {O S X : Type} [CommRing O] [AddCommGroup S] [Module O S] (𝒜 : X → Submodule O S)
    (h : iSupIndep 𝒜) (p : X → Prop) [DecidablePred p] :
    ∃ P : S → S, P 0 = 0 ∧ (∀ a ∈ ⨆ j, 𝒜 j, ∀ b ∈ ⨆ j, 𝒜 j, P (a + b) = P a + P b) ∧
      ∀ j, ∀ a ∈ 𝒜 j, P a = if p j then a else 0 := by
  classical
  let L := DFinsupp.lsum ℕ (fun i => (𝒜 i).subtype)
  let Q := DFinsupp.lsum ℕ (fun i => if p i then (𝒜 i).subtype else (0 : 𝒜 i →ₗ[O] S))
  have hL : Function.Injective L := h.dfinsupp_lsum_injective
  let P : S → S := fun t => if ht : ∃ y, L y = t then Q ht.choose else 0
  have hP : ∀ y, P (L y) = Q y := fun y => by
    have ht : ∃ y', L y' = L y := ⟨y, rfl⟩
    show (if ht : ∃ y', L y' = L y then Q ht.choose else 0) = Q y
    rw [dif_pos ht, hL ht.choose_spec]
  have hmem : ∀ a ∈ ⨆ j, 𝒜 j, ∃ y, L y = a := fun a ha => by
    rw [Submodule.iSup_eq_range_dfinsupp_lsum] at ha
    exact LinearMap.mem_range.1 ha
  refine ⟨P, ?_, ?_, ?_⟩
  · have h0 := hP 0
    rwa [map_zero, map_zero] at h0
  · intro a ha b hb
    obtain ⟨ya, rfl⟩ := hmem a ha
    obtain ⟨yb, rfl⟩ := hmem b hb
    rw [← map_add, hP, hP, hP, map_add]
  · intro j a ha
    have e : L (DFinsupp.single j ⟨a, ha⟩) = a := by
      simp [L]
    conv_lhs => rw [← e]
    rw [hP]
    simp only [Q, DFinsupp.lsum_single]
    split_ifs <;> simp

theorem UpperTheory.V.GradeZeroInterpolatingElement.ptLift :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c), D.Good → ∀ M : Model D, ∀ x : M.A →ₐ[c.O] PadicAlgCl l, OnS M.eqns.ideal x → ∃ ξ : M.SS →ₐ[c.O] PadicAlgCl l, ξ.comp M.toSS = x := by
  intro Ω _ _ _ l _ c D hD M x hx
  obtain ⟨hind, ⟨s, hs1, hs2⟩, -⟩ := sInternal D hD M
  obtain ⟨hk1, hk2, -⟩ := kerA D hD M
  obtain ⟨P, hP0, hPadd, hPj⟩ := exists_proj M.sPart hind (fun j : ℤ × ℤ => j.1 = 0)
  have hz0 : ((M.toSS 0 : M.SS) : M.S) = 0 := by
    have e0 : M.toSS 0 = 0 := M.toSS.map_zero
    rw [e0]
    rfl
  have hPS : ∀ y ∈ ⨆ j, M.sPart j, P y ∈ ⨆ j, M.sPart j ∧ ∃ f : M.A, (M.toSS f : M.S) = P y := by
    intro y hy
    induction hy using Submodule.iSup_induction' with
    | mem j y hy =>
      rw [hPj j y hy]
      split_ifs with hj
      · refine ⟨Submodule.mem_iSup_of_mem j hy, ?_⟩
        obtain ⟨j1, j2⟩ := j
        simp only at hj
        subst hj
        obtain ⟨f, -, hf⟩ := hk2 j2 ⟨y, M.sPart_le hy⟩ hy
        exact ⟨f, congrArg Subtype.val hf⟩
      · exact ⟨zero_mem _, 0, hz0⟩
    | zero =>
      rw [hP0]
      exact ⟨zero_mem _, 0, hz0⟩
    | add a b ha hb iha ihb =>
      rw [hPadd a ha b hb]
      obtain ⟨h1, f1, hf1⟩ := iha
      obtain ⟨h2, f2, hf2⟩ := ihb
      refine ⟨add_mem h1 h2, f1 + f2, ?_⟩
      have e : M.toSS (f1 + f2) = M.toSS f1 + M.toSS f2 := M.toSS.map_add f1 f2
      rw [← hf1, ← hf2, e]
      rfl
  have hπm : ∀ g ∈ ⨆ n, M.aPart n, ∀ y ∈ ⨆ j, M.sPart j, M.π g * y ∈ ⨆ j, M.sPart j :=
    fun g hg y hy => M.SS.mul_mem (M.π_mem ⟨g, hg⟩) hy
  have hPmul : ∀ g ∈ ⨆ n, M.aPart n, ∀ y ∈ ⨆ j, M.sPart j, P (M.π g * y) = M.π g * P y := by
    intro g hg
    induction hg using Submodule.iSup_induction' with
    | mem n g hg =>
      intro y hy
      have hg' : g ∈ ⨆ n, M.aPart n := Submodule.mem_iSup_of_mem n hg
      induction hy using Submodule.iSup_induction' with
      | mem j y hy =>
        have hπ : M.π g ∈ M.sPart (0, n) := Submodule.mem_map_of_mem (f := M.π.toLinearMap) hg
        have hgy : M.π g * y ∈ M.sPart ((0, n) + j) := SetLike.GradedMul.mul_mem hπ hy
        rw [hPj _ _ hgy, hPj _ _ hy]
        simp only [Prod.fst_add, zero_add]
        split_ifs <;> simp
      | zero => rw [mul_zero, hP0, mul_zero]
      | add a b ha hb iha ihb =>
        rw [mul_add, hPadd _ (hπm g hg' a ha) _ (hπm g hg' b hb), iha, ihb, hPadd a ha b hb, mul_add]
    | zero =>
      intro y hy
      have e0 : M.π 0 = 0 := M.π.map_zero
      rw [e0, zero_mul, hP0, zero_mul]
    | add g h hg hh ihg ihh =>
      intro y hy
      have e : M.π (g + h) = M.π g + M.π h := M.π.map_add g h
      rw [e, add_mul, hPadd _ (hπm g hg y hy) _ (hπm h hh y hy), ihg y hy, ihh y hy, add_mul]
  let P' : M.SS →+ M.SS :=
    { toFun := fun y => ⟨P y.1, (hPS y.1 y.2).1⟩
      map_zero' := Subtype.ext hP0
      map_add' := fun a b => Subtype.ext (hPadd _ a.2 _ b.2) }
  have h1P : P 1 = 1 := by
    have h1 := hPj 0 1 SetLike.GradedOne.one_mem
    simpa using h1
  let s' : Set M.SS := Subtype.val ⁻¹' (s : Set M.S)
  have hs' : s'.Finite := s.finite_toSet.preimage Subtype.val_injective.injOn
  have hgen : Algebra.adjoin c.O (Set.range M.toSS ∪ s') = ⊤ := by
    rw [eq_top_iff]
    rintro y -
    have key : Algebra.adjoin c.O ((M.sPart 0 : Set M.S) ∪ (s : Set M.S)) ≤
        (Algebra.adjoin c.O (Set.range M.toSS ∪ s')).map M.SS.val := by
      apply Algebra.adjoin_le
      rintro z (hz | hz)
      · obtain ⟨f, -, hf⟩ := hk2 0 ⟨z, M.sPart_le hz⟩ hz
        exact Subalgebra.mem_map.2 ⟨⟨z, M.sPart_le hz⟩, Algebra.subset_adjoin (Or.inl ⟨f, hf⟩), rfl⟩
      · obtain ⟨w, hw⟩ := hs1 z hz
        exact Subalgebra.mem_map.2 ⟨⟨z, M.sPart_le hw⟩, Algebra.subset_adjoin (Or.inr hz), rfl⟩
    have hy : (y : M.S) ∈ Algebra.adjoin c.O ((M.sPart 0 : Set M.S) ∪ (s : Set M.S)) := by
      rw [hs2]
      exact y.2
    obtain ⟨z, hz, hzy⟩ := Subalgebra.mem_map.1 (key hy)
    have hzy' : z = y := Subtype.ext hzy
    rw [← hzy']
    exact hz
  exact ext_of_proj M.toSS x (fun f hf => hx f ((hk1 f).1 hf)) P'
    (fun f y => Subtype.ext (hPmul f.1 f.2 y.1 y.2))
    (fun y => ⟨(hPS y.1 y.2).2.choose, Subtype.ext (hPS y.1 y.2).2.choose_spec⟩)
    (Subtype.ext h1P) s' hs' hgen

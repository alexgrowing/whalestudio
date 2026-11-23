import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.CrystallineTowers.LocTower

noncomputable section

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC TensorProduct
open Formalism.BasicNotions.Loc Formalism.MainNotions.N CrystallineSemistableComparison UpperTheory.Gal.Int.Geo
open GlobalTheory.GalV (HTower Htot hop galV galTot pullTot)
open UpperTheory.Gal.Seam

open TensorProduct in
private theorem core {Q L : Type*} [Field Q] [Field L] [Algebra Q L] {V : ℤ → Type*} [∀ n, AddCommGroup (V n)] [∀ n, Module Q (V n)]
    (hneg : ∀ n : ℤ, n < 0 → Subsingleton (V n)) (hfin : ∀ n, FiniteDimensional Q (V n))
    {U G : Type*} [AddCommGroup U] [Module L U] (g : G → ∀ n, V n →ₗ[Q] V n)
    (φ : (L ⊗[Q] DirectSum ℤ V) →ₗ[L] U) (hφ : Function.Injective φ) (gU : G → U →ₗ[L] U)
    (hc : ∀ σ, gU σ ∘ₗ φ = φ ∘ₗ (DirectSum.lmap (g σ)).baseChange L)
    {d : ℕ} (v : Fin d → U) (hv : LinearIndependent L v) (hr : ∀ j, v j ∈ LinearMap.range φ)
    (ρ : G → Matrix (Fin d) (Fin d) L) (hρ : ∀ σ j, gU σ (v j) = ∑ i, ρ σ i j • v i) :
    ∃ (N : ℕ) (a : Fin N → ℕ) (b : ∀ n : Fin N, Module.Basis (Fin (a n)) Q (V ((n : ℕ) : ℤ)))
      (M : Matrix (Σ n, Fin (a n)) (Fin d) L), Function.Injective M.mulVec ∧ ∀ σ,
        (Matrix.blockDiagonal' fun n : Fin N => LinearMap.toMatrix (b n) (b n) (g σ ((n : ℕ) : ℤ))).map (algebraMap Q L) * M =
          M * ρ σ := by
  classical
  choose y hy using hr
  let e := TensorProduct.directSumRight Q L L V
  let π : ∀ n : ℤ, (L ⊗[Q] DirectSum ℤ V) →ₗ[L] L ⊗[Q] V n := fun n =>
    (DirectSum.component L ℤ (fun i => L ⊗[Q] V i) n) ∘ₗ e.toLinearMap
  have hπ0 : ∀ w, (∀ n, π n w = 0) → w = 0 := fun w h => by
    apply e.injective
    rw [map_zero]
    exact DFinsupp.ext fun n => h n
  have hπt : ∀ (n : ℤ) (t : L) (x : DirectSum ℤ V), π n (t ⊗ₜ[Q] x) = t ⊗ₜ[Q] (x n) := fun n t x => by
    induction x using DirectSum.induction_on with
    | zero => simp
    | of i z =>
      have h1 : π n (t ⊗ₜ[Q] (DirectSum.of V i z)) =
          DirectSum.component L ℤ (fun i => L ⊗[Q] V i) n (DirectSum.lof L ℤ (fun i => L ⊗[Q] V i) i (t ⊗ₜ[Q] z)) := by
        change DirectSum.component L ℤ (fun i => L ⊗[Q] V i) n (e (t ⊗ₜ[Q] (DirectSum.lof Q ℤ V i z))) = _
        rw [TensorProduct.directSumRight_tmul_lof]
      rw [h1]
      by_cases hi : i = n
      · subst hi
        rw [DirectSum.component.lof_self]
        simp
      · change (DirectSum.lof L ℤ (fun i => L ⊗[Q] V i) i (t ⊗ₜ[Q] z)) n = _
        rw [DirectSum.lof_eq_of, DirectSum.of_eq_of_ne _ _ _ (Ne.symm hi), DirectSum.of_eq_of_ne _ _ _ (Ne.symm hi),
          TensorProduct.tmul_zero]
    | add x₁ x₂ h₁ h₂ =>
      rw [TensorProduct.tmul_add, map_add, h₁, h₂, DirectSum.add_apply, TensorProduct.tmul_add]
  have hnat : ∀ σ n w, π n ((DirectSum.lmap (g σ)).baseChange L w) = (g σ n).baseChange L (π n w) := fun σ n w => by
    induction w using TensorProduct.induction_on with
    | zero => simp
    | tmul t x =>
      rw [LinearMap.baseChange_tmul, hπt, hπt, LinearMap.baseChange_tmul, DirectSum.lmap_apply]
    | add a b ha hb => simp only [map_add, ha, hb]
  have hsupp : ∀ w, ∃ N : ℕ, ∀ n : ℤ, (N : ℤ) ≤ n → π n w = 0 := fun w => by
    refine ⟨(DFinsupp.support (e w)).sup Int.toNat + 1, fun n hn => ?_⟩
    by_contra h
    have hm : n ∈ DFinsupp.support (e w) := DFinsupp.mem_support_iff.2 h
    have := Finset.le_sup (f := Int.toNat) hm
    push_cast at hn
    omega
  have hnegπ : ∀ (n : ℤ) w, n < 0 → π n w = 0 := fun n w hn => by
    haveI := hneg n hn
    generalize π n w = u
    induction u using TensorProduct.induction_on with
    | zero => rfl
    | tmul t x => rw [Subsingleton.elim x 0, TensorProduct.tmul_zero]
    | add a b ha hb => rw [ha, hb, add_zero]
  choose Nf hNf using fun j => hsupp (y j)
  let N := Finset.univ.sup Nf
  have hbig : ∀ j (n : ℤ), (N : ℤ) ≤ n → π n (y j) = 0 := fun j n hn =>
    hNf j n (le_trans (by exact_mod_cast Finset.le_sup (f := Nf) (Finset.mem_univ j)) hn)
  let a : Fin N → ℕ := fun n => Module.finrank Q (V ((n : ℕ) : ℤ))
  let b : ∀ n : Fin N, Module.Basis (Fin (a n)) Q (V ((n : ℕ) : ℤ)) := fun n => Module.finBasis Q _
  let B : ∀ n : Fin N, Module.Basis (Fin (a n)) L (L ⊗[Q] V ((n : ℕ) : ℤ)) := fun n => Algebra.TensorProduct.basis L (b n)
  let M : Matrix (Σ n, Fin (a n)) (Fin d) L := fun p j => (B p.1).repr (π _ (y j)) p.2
  have hG : ∀ σ j, (DirectSum.lmap (g σ)).baseChange L (y j) = ∑ i, ρ σ i j • y i := fun σ j => by
    apply hφ
    have h := LinearMap.congr_fun (hc σ) (y j)
    simp only [LinearMap.comp_apply] at h
    rw [← h, hy, hρ, map_sum]
    simp only [map_smul, hy]
  have key : ∀ c : Fin d → L, M.mulVec c = 0 → c = 0 := fun c hcz => by
    have hw : (∑ j, c j • y j) = 0 := by
      apply hπ0
      intro m
      simp only [map_sum, map_smul]
      rcases lt_or_ge m 0 with hm | hm
      · simp [hnegπ m _ hm]
      rcases lt_or_ge m (N : ℤ) with hN | hN
      · obtain ⟨k, rfl⟩ := Int.eq_ofNat_of_zero_le hm
        have hk : k < N := by exact_mod_cast hN
        let n : Fin N := ⟨k, hk⟩
        apply (B n).repr.injective
        ext i
        have := congrFun hcz ⟨n, i⟩
        simp only [Matrix.mulVec, dotProduct, Pi.zero_apply] at this
        simp only [map_sum, map_smul, map_zero, Finsupp.coe_finset_sum, Finset.sum_apply, Finsupp.coe_smul,
          Pi.smul_apply, smul_eq_mul, Finsupp.coe_zero, Pi.zero_apply]
        rw [← this]
        exact Finset.sum_congr rfl fun j _ => mul_comm _ _
      · simp [hbig _ m hN]
    have h0 : ∑ j, c j • v j = 0 := by
      have := congrArg φ hw
      simpa [map_sum, hy] using this
    funext j
    exact Fintype.linearIndependent_iff.1 hv c h0 j
  refine ⟨N, a, b, M, fun c c' h => ?_, fun σ => ?_⟩
  · have := key (c - c') (by rw [Matrix.mulVec_sub, h, sub_self])
    exact sub_eq_zero.1 this
  · ext ⟨n, i⟩ j
    have h1 : (B n).repr ((g σ ((n : ℕ) : ℤ)).baseChange L (π _ (y j))) i =
        ∑ k, algebraMap Q L (LinearMap.toMatrix (b n) (b n) (g σ ((n : ℕ) : ℤ)) i k) * (B n).repr (π _ (y j)) k := by
      rw [← LinearMap.toMatrix_mulVec_repr (B n) (B n)]
      simp only [B, LinearMap.toMatrix_baseChange]
      rfl
    have h2 : (g σ ((n : ℕ) : ℤ)).baseChange L (π _ (y j)) = ∑ i', ρ σ i' j • π _ (y i') := by
      rw [← hnat, hG, map_sum]
      simp only [map_smul]
    rw [h2] at h1
    simp only [map_sum, map_smul, Finsupp.coe_finset_sum, Finset.sum_apply, Finsupp.coe_smul,
      Pi.smul_apply, smul_eq_mul] at h1
    rw [Matrix.mul_apply, Matrix.mul_apply, Fintype.sum_sigma, Finset.sum_eq_single n]
    · simp only [Matrix.map_apply, Matrix.blockDiagonal'_apply_eq]
      rw [← h1]
      exact Finset.sum_congr rfl fun x _ => mul_comm _ _
    · intro m _ hm
      refine Finset.sum_eq_zero fun k _ => ?_
      simp [Matrix.blockDiagonal'_apply_ne _ _ _ hm.symm]
    · simp

theorem UpperTheory.Gal.Seam.matInS :
    GlobalTheory.GalV.VFin → PieceIn → NegVan → MatIn := by
  intro hV hP hN l _ K H θ hH C hC d ρ₁ hM
  obtain ⟨hinj, hle, heq⟩ := hP l K.1 (Om l) H θ hH C hC
  obtain ⟨b, hb⟩ := hM
  haveI hpr : IsProper C.p := by
    obtain ⟨n, i, hi, e⟩ := C.proj
    haveI := hi
    haveI := ReciprocityTheory.ChartRestriction.G.Geo.Tor.isProper_str ↥(OK l K.1) n
    rw [← e]
    infer_instance
  haveI hq : IsProper (mod C).q := by
    change IsProper (pullback.snd C.p _)
    infer_instance
  haveI hg : IsProper (pullback.snd (mod C).q (Spec.map (CommRingCat.ofHom (algebraMap ↥K.1 (PadicAlgCl l))))) := inferInstance
  have hunit : IsUnit ((l : ℕ) : PadicAlgCl l) :=
    (Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero).isUnit
  have hfin := fun n : ℤ => (hV l (PadicAlgCl l) hunit
    (pullback.snd (mod C).q (Spec.map (CommRingCat.ofHom (algebraMap ↥K.1 (PadicAlgCl l))))) n 0).2
  obtain ⟨N, a, c, M, hMi, hMe⟩ := core (Q := ℚ_[l]) (L := Om l)
    (V := fun n : ℤ => HQ l (sch.obj (GlobalTheory.Et.geom (PadicAlgCl l) (mod C).q)) n 0) (G := ↥(GK K))
    (fun n hn => hN l _ n hn) hfin
    (fun σ n => galHQ l (PadicAlgCl l) (mod C).q n 0 (IntermediateField.fixingSubgroupEquiv K.1 σ))
    ((pullTot l (sch.map (toMod C))).baseChange (Om l)) hinj
    (fun σ => galV l H (PadicAlgCl l) (Om l) (IntermediateField.fixingSubgroupEquiv K.1 σ))
    (fun σ => by
      have h := heq (IntermediateField.fixingSubgroupEquiv K.1 σ)
      have h2 := congrArg (LinearMap.baseChange (Om l)) h
      rw [LinearMap.baseChange_comp, LinearMap.baseChange_comp] at h2
      exact h2)
    (fun j => (b j).1)
    (b.linearIndependent.map' (Submodule.subtype _) (Submodule.ker_subtype _))
    (fun j => hle (b j).2)
    (fun σ => (ρ₁ (IntermediateField.fixingSubgroupEquiv K.1 σ) : Matrix (Fin d) (Fin d) (Om l)))
    (fun σ j => hb _ j)
  exact ⟨N, a, c, M, hMi, fun σ => hMe σ⟩

import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.CrystallineTowers.LocTower
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PBcGal
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PBcSplits
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PSplitsBasic
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PSplitsPts
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PIsoPts
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PPtsOfSplits

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC GlobalTheory.GalV TensorProduct
open UpperTheory.Gal.Seam

private theorem tot_inj (hV : VInv) (l : ℕ) [Fact l.Prime] {W Z : Scheme.{0}} (c : W ⟶ Z) (G : Type) [Group G] [Finite G]
    (a : G → (W ⟶ W)) (h : IsGalois c G a) : Function.Injective (pullTot l (sch.map c)) := by
  obtain ⟨h1, h2, h3, -, -, hs, hi⟩ := h
  letI : Fintype G := Fintype.ofFinite G
  exact (DirectSum.lmap_injective _).2 fun n => (hV l c G a hs hi n 0).1

private theorem tot_range (hV : VInv) (l : ℕ) [Fact l.Prime] {W Z : Scheme.{0}} (c : W ⟶ Z) (G : Type) [Group G] [Finite G]
    (a : G → (W ⟶ W)) (h : IsGalois c G a) (x : Htot l (sch.obj W))
    (hx : ∀ g, pullTot l (sch.map (a g)) x = x) : x ∈ LinearMap.range (pullTot l (sch.map c)) := by
  classical
  obtain ⟨h1, h2, h3, -, -, hs, hi⟩ := h
  letI : Fintype G := Fintype.ofFinite G
  have key : ∀ n : ℤ, x n ∈ LinearMap.range (pullHQ l (sch.map c) n 0) := fun n => by
    rw [(hV l c G a hs hi n 0).2]
    refine (Submodule.mem_iInf _).2 fun g => ?_
    have e := congrArg (fun u : Htot l (sch.obj W) => u n) (hx g)
    simp only [pullTot, DirectSum.lmap_apply] at e
    simp [LinearMap.mem_ker, sub_eq_zero, e]
  rw [← DirectSum.sum_support_of x]
  refine Submodule.sum_mem _ fun n _ => ?_
  obtain ⟨z, hz⟩ := key n
  refine ⟨DirectSum.lof ℚ_[l] ℤ (fun n => HQ l (sch.obj Z) n 0) n z, ?_⟩
  rw [pullTot, DirectSum.lmap_lof, hz]
  rfl

private theorem corr_iso (hV : VInv) (l : ℕ) [Fact l.Prime] {Z Y : Scheme.{0}} [Nonempty Z] (s : Y ⟶ Z) [IsIso s] (b : Z ⟶ Z)
    (A : Htot l (sch.obj Z) →ₗ[ℚ_[l]] Htot l (sch.obj Z)) (h : IsCorrOp l s (s ≫ b) A) :
    A = pullTot l (sch.map b) := by
  obtain ⟨W, c, G, _, _, a, J, _, σ, hG, hS, hx⟩ := h
  have hinj := tot_inj hV l c G a hG
  have hsur : Surjective c := hG.2.2.1
  obtain ⟨hσ, -⟩ := id hS
  obtain ⟨z⟩ := ‹Nonempty Z›
  obtain ⟨w, -⟩ := hsur.surj z
  let pt : UpperTheory.Gal.G3.sp (W.residueField w) ⟶ W := W.fromSpecResidueField w
  obtain ⟨j₀, -, hj⟩ := UpperTheory.Gal.G3.pPtsOfSplits s c J σ hS (W.residueField w) pt (pt ≫ c ≫ inv s) (by simp)
  have hall : ∀ j, j = j₀ := fun j => hj j (by
    have : σ j = c ≫ inv s := by rw [← hσ j]; simp
    change pt ≫ σ j = pt ≫ c ≫ inv s
    rw [this])
  haveI : Unique J := ⟨⟨j₀⟩, hall⟩
  refine LinearMap.ext fun x => hinj ?_
  rw [hx x, Fintype.sum_unique]
  have e : σ default ≫ s ≫ b = c ≫ b := by rw [← Category.assoc, hσ]
  rw [e, Functor.map_comp, pullTot_comp]
  rfl

private theorem gal_nat {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω] {X Y : Scheme.{0}} {p : X ⟶ Spec (CommRingCat.of k)}
    {q : Y ⟶ Spec (CommRingCat.of k)} (u : X ⟶ Y) (hu : u ≫ q = p) (σ : Ω ≃ₐ[k] Ω) :
    GlobalTheory.Et.galMap Ω p σ ≫ GlobalTheory.Et.geomMap Ω p u hu = GlobalTheory.Et.geomMap Ω p u hu ≫ GlobalTheory.Et.galMap Ω q σ := by
  have f1 : GlobalTheory.Et.geomMap Ω p u hu ≫ pullback.fst _ _ = pullback.fst _ _ ≫ u := pullback.lift_fst _ _ _
  have f2 : GlobalTheory.Et.geomMap Ω p u hu ≫ pullback.snd _ _ = pullback.snd _ _ := pullback.lift_snd _ _ _
  apply pullback.hom_ext
  · rw [Category.assoc, f1, GlobalTheory.Et.galMap_fst_assoc, Category.assoc, GlobalTheory.Et.galMap_fst, f1]
  · rw [Category.assoc, f2, GlobalTheory.Et.galMap_snd, Category.assoc, GlobalTheory.Et.galMap_snd, ← Category.assoc, f2]

private theorem bc_range {R L M M' N : Type*} [CommRing R] [CommRing L] [Algebra R L] [AddCommGroup M] [AddCommGroup M']
    [AddCommGroup N] [Module R M] [Module R M'] [Module R N] (E : M →ₗ[R] N) (P : M' →ₗ[R] N)
    (h : ∀ m, E m ∈ LinearMap.range P) (w : L ⊗[R] M) : E.baseChange L w ∈ LinearMap.range (P.baseChange L) := by
  induction w using TensorProduct.induction_on with
  | zero => simp
  | tmul a m =>
    obtain ⟨n, hn⟩ := h m
    exact ⟨a ⊗ₜ n, by simp [hn]⟩
  | add x y hx hy =>
    rw [map_add]
    exact Submodule.add_mem _ hx hy

private theorem bc_sum {R L M N J : Type*} [CommRing R] [CommRing L] [Algebra R L] [AddCommGroup M] [AddCommGroup N]
    [Module R M] [Module R N] (s : Finset J) (A : J → M →ₗ[R] N) (w : L ⊗[R] M) :
    (∑ j ∈ s, A j).baseChange L w = ∑ j ∈ s, (A j).baseChange L w := by
  induction w using TensorProduct.induction_on with
  | zero => simp
  | tmul a m => simp [TensorProduct.tmul_sum]
  | add x y hx hy => simp only [map_add, hx, hy, Finset.sum_add_distrib]

private theorem inv_mem (hV : VInv) (l : ℕ) [Fact l.Prime] {W Z : Scheme.{0}} (f : W ⟶ Z) (G : Type) [Group G] [Finite G]
    (b : G → (W ⟶ W)) (hG : IsGalois f G b) (L : Type) [Field L] [Algebra ℚ_[l] L] (y : L ⊗[ℚ_[l]] Htot l (sch.obj W))
    (hinv : ∀ δ, (pullTot l (sch.map (b δ))).baseChange L y = y) :
    y ∈ LinearMap.range ((pullTot l (sch.map f)).baseChange L) := by
  letI : Fintype G := Fintype.ofFinite G
  haveI : CharZero L := charZero_of_injective_algebraMap (algebraMap ℚ_[l] L).injective
  have hmul : ∀ δ δ' m, pullTot l (sch.map (b δ')) (pullTot l (sch.map (b δ)) m) = pullTot l (sch.map (b (δ' * δ))) m := by
    intro δ δ' m
    rw [hG.2.2.2.2.1, Functor.map_comp, pullTot_comp]
    rfl
  have hE : ∀ m, (∑ δ, pullTot l (sch.map (b δ))) m ∈ LinearMap.range (pullTot l (sch.map f)) := fun m => by
    refine tot_range hV l _ G b hG _ fun δ' => ?_
    rw [LinearMap.sum_apply, map_sum]
    simp only [hmul]
    exact Fintype.sum_equiv (Equiv.mulLeft δ') _ _ fun _ => rfl
  have hEy : (∑ δ, pullTot l (sch.map (b δ))).baseChange L y = ((Fintype.card G : ℕ) : L) • y := by
    rw [bc_sum, Finset.sum_congr rfl fun δ _ => hinv δ, Finset.sum_const, Finset.card_univ, Nat.cast_smul_eq_nsmul]
  have hcard : ((Fintype.card G : ℕ) : L) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hy' : y = ((Fintype.card G : ℕ) : L)⁻¹ • (∑ δ, pullTot l (sch.map (b δ))).baseChange L y := by
    rw [hEy, smul_smul, inv_mul_cancel₀ hcard, one_smul]
  rw [hy']
  exact Submodule.smul_mem _ _ (bc_range _ _ hE y)

private theorem empty_mem (l : ℕ) [Fact l.Prime] {W Z : Scheme.{0}} [IsEmpty ↑W] (f : W ⟶ Z) (hs : Surjective f) (L : Type)
    [Field L] [Algebra ℚ_[l] L] (y : L ⊗[ℚ_[l]] Htot l (sch.obj W)) :
    y ∈ LinearMap.range ((pullTot l (sch.map f)).baseChange L) := by
  haveI : IsEmpty ↑Z := ⟨fun z => by
    obtain ⟨w, -⟩ := hs.surj z
    exact isEmptyElim w⟩
  haveI : IsIso f := isIso_of_isEmpty _
  have hsur : ∀ m, (LinearMap.id : Htot l (sch.obj W) →ₗ[ℚ_[l]] _) m ∈ LinearMap.range (pullTot l (sch.map f)) := fun m => by
    refine ⟨pullTot l (sch.map (inv f)) m, ?_⟩
    have e : pullTot l (sch.map f) ∘ₗ pullTot l (sch.map (inv f)) = LinearMap.id := by
      rw [← pullTot_comp, ← Functor.map_comp, IsIso.hom_inv_id, CategoryTheory.Functor.map_id, pullTot_id]
    exact LinearMap.congr_fun e m
  have h2 := bc_range (L := L) _ _ hsur y
  rwa [LinearMap.baseChange_id, LinearMap.id_apply] at h2

theorem UpperTheory.Gal.Seam.pieceInS :
    GlobalTheory.GalV.VInv → HopEx → PieceIn := by
  intro hT hHop l _ K L _ _ H θ hN C hOn
  have hV := hT
  have hGK : IsGalois (UpperTheory.Gal.G3.piK C) C.Δ C.a := C.isGalois hOn
  have ha : ∀ δ, C.a δ ≫ H.q = H.q := fun δ => by
    rw [← UpperTheory.Gal.G3.piK_snd C, ← Category.assoc, hGK.2.2.2.2.2.choose δ]
  let g₀ : UpperTheory.Gal.G3.sp (PadicAlgCl l) ⟶ UpperTheory.Gal.G3.sp ↥K :=
    Spec.map (CommRingCat.ofHom (algebraMap ↥K (PadicAlgCl l)))
  let b : C.Δ → (H.geomZ (PadicAlgCl l) ⟶ H.geomZ (PadicAlgCl l)) := fun δ => UpperTheory.Gal.G3.bcMap g₀ (C.a δ) (ha δ)
  have hG : IsGalois (toMod C) C.Δ b :=
    UpperTheory.Gal.G3.pBcGal (UpperTheory.Gal.G3.pBcSplits (UpperTheory.Gal.G3.pSplitsBasic (UpperTheory.Gal.G3.pSplitsPts UpperTheory.Gal.G3.pIsoPts)
      UpperTheory.Gal.G3.pPtsOfSplits)) g₀ _ _ (UpperTheory.Gal.G3.piK C) (UpperTheory.Gal.G3.piK_snd C) C.Δ C.a ha hGK
  refine ⟨?_, ?_, fun σ => ?_⟩
  · rw [LinearMap.baseChange_eq_ltensor]
    exact Module.Flat.lTensor_preserves_injective_linearMap _ (tot_inj hV l _ C.Δ b hG)
  · intro y hy
    by_cases hZ : Nonempty ↑(H.geomZ (PadicAlgCl l))
    · have hop' : ∀ δ, ∃ g, hop l H (PadicAlgCl l) g = pullTot l (sch.map (b δ)) ∧ θ g = 1 := fun δ => by
        obtain ⟨g, hiso, ht, hθ⟩ := C.fix δ
        haveI : IsIso (H.sΩ (PadicAlgCl l) g) := GlobalTheory.GalV.GaloisTowerConditions.geomMap_isIso (PadicAlgCl l) (H.s g) rfl
        have b1 : b δ ≫ pullback.fst H.q g₀ = pullback.fst H.q g₀ ≫ C.a δ := UpperTheory.Gal.G3.bcMap_fst g₀ (C.a δ) (ha δ)
        have b2 : b δ ≫ pullback.snd H.q g₀ = pullback.snd H.q g₀ := UpperTheory.Gal.G3.bcMap_snd g₀ (C.a δ) (ha δ)
        have t' : H.tΩ (PadicAlgCl l) g = UpperTheory.Gal.G3.bcMap g₀ (H.t g) (H.comm g) := rfl
        have s' : H.sΩ (PadicAlgCl l) g = UpperTheory.Gal.G3.bcMap g₀ (H.s g) rfl := rfl
        have e : H.tΩ (PadicAlgCl l) g = H.sΩ (PadicAlgCl l) g ≫ b δ := by
          rw [t', s']
          apply pullback.hom_ext
          · rw [UpperTheory.Gal.G3.bcMap_fst, Category.assoc, b1, ← Category.assoc, UpperTheory.Gal.G3.bcMap_fst, Category.assoc, ht]
          · rw [UpperTheory.Gal.G3.bcMap_snd, Category.assoc, b2, UpperTheory.Gal.G3.bcMap_snd]
        have hc := hHop l ↥K (PadicAlgCl l) H hN g
        rw [e] at hc
        exact ⟨g, corr_iso hV l (H.sΩ (PadicAlgCl l) g) (b δ) _ hc, hθ⟩
      have hinv : ∀ δ, (pullTot l (sch.map (b δ))).baseChange L y = y := fun δ => by
        obtain ⟨g, e, hθ⟩ := hop' δ
        have h1 := Module.End.mem_eigenspace_iff.1 ((Submodule.mem_iInf _).1 hy g)
        rw [hθ, one_smul, e] at h1
        exact h1
      exact inv_mem hV l _ C.Δ b hG L y hinv
    · haveI : IsEmpty ↑(H.geomZ (PadicAlgCl l)) := not_nonempty_iff.1 hZ
      exact empty_mem l _ hG.2.2.1 L y
  · change pullTot l (sch.map _) ∘ₗ pullTot l (sch.map _) = pullTot l (sch.map _) ∘ₗ pullTot l (sch.map _)
    rw [← pullTot_comp, ← pullTot_comp, ← Functor.map_comp, ← Functor.map_comp]
    congr 2
    exact gal_nat _ _ σ

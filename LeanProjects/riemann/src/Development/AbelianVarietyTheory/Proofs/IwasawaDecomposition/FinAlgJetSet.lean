import Mathlib
import Formalism.LocalToGlobal.KernelLattices.ThDistC
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.ThDistC
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FinAlgOfFinite
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DerivAt0CompMem
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFinsetSdLatReps
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteSemilocalHomLatticeClassesMod
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.Mem.Col2.JetEx

namespace GlobalTheory.Mem.Col2.JetFin

theorem finAlg_range {E : Type} [Field E] [NumberField E] (f : E →+* ℂ) : FinAlg (Set.range f) := by
  classical
  let b := Module.finBasis ℚ E
  refine (finAlg_of_finite (T := Set.range (f ∘ b)) (Set.finite_range _) ?_).closure.mono ?_
  · rintro _ ⟨i, rfl⟩
    exact (Algebra.IsAlgebraic.isAlgebraic (R := ℚ) (b i)).algHom f.toRatAlgHom
  · rintro _ ⟨x, rfl⟩
    rw [← b.sum_repr x, map_sum]
    refine sum_mem fun i _ => ?_
    rw [map_rat_smul, Rat.smul_def]
    exact mul_mem (SubfieldClass.ratCast_mem _ _) (Subfield.subset_closure ⟨i, rfl⟩)

variable {X : Fields} (A : Amb X) {a b : ℕ} (S : Finset (HeightOneSpectrum (𝓞 X.E)))

theorem thInd_congr (N : Submodule (𝓞 X.E) (Sp X.E a)) (N' : Submodule (𝓞 X.E) (Sp X.E b)) (c : ℕ) (x x' : HomE X.E a b)
    (h : x - x' ∈ mulLat c (homAt S N N')) : A.thInd S N N' c x = A.thInd S N N' c x' := by
  unfold Amb.thInd Amb.liftW
  rw [isLift_congr A S N N' c x x' h]

theorem finite_thInd (N : Submodule (𝓞 X.E) (Sp X.E a)) (N' : Submodule (𝓞 X.E) (Sp X.E b)) (M c : ℕ)
    (hN : IsSdLat N) (hN' : IsSdLat N') (hM : 0 < M) (hc : 0 < c) :
    (A.thInd S N N' c '' (divLat M (homAt S N N') : Set (HomE X.E a b))).Finite := by
  have := (GlobalTheory.SemilocalClasses.finite_card_classes X.E a b S N N' M c hN.1 hN'.1 hM hc).1
  refine (Set.finite_range fun q : (↥(divLat M (homAt S N N')) ⧸ (mulLat c (homAt S N N')).comap (divLat M (homAt S N N')).subtype) =>
    A.thInd S N N' c (Quotient.out q).1).subset ?_
  rintro _ ⟨x, hx, rfl⟩
  refine ⟨Submodule.Quotient.mk ⟨x, hx⟩, thInd_congr A S N N' c _ _ ?_⟩
  have := (Submodule.Quotient.eq ((mulLat c (homAt S N N')).comap (divLat M (homAt S N N')).subtype)).1
    (Quotient.out_eq (Submodule.Quotient.mk ⟨x, hx⟩ : (↥(divLat M (homAt S N N')) ⧸ (mulLat c (homAt S N N')).comap (divLat M (homAt S N N')).subtype)))
  exact this

noncomputable def pullLin (γ : Sp X.E a ≃ₗ[X.E] Sp X.E a) (γ' : Sp X.E b ≃ₗ[X.E] Sp X.E b) : VCx X.Tau a b →ₗ[ℂ] VCx X.Tau a b where
  toFun := A.pullV a b γ γ'
  map_add' z w := by
    funext τ i j
    simp only [Amb.pullV, Pi.add_apply, mul_add, add_mul, Finset.sum_add_distrib]
  map_smul' t z := by
    funext τ i j
    simp only [Amb.pullV, Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => by ring

theorem finAlg_jetSet : ∀ (X : Fields) (A : Amb X) (a b : ℕ) (S : Finset (HeightOneSpectrum (𝓞 X.E))) (M n : ℕ), X.Ok → 0 < M → A.ESmooth a b → A.ThIndEq a b S M → A.ChiLaw a b → JetAlg A a b S M → (∀ τ, IsAlgebraic ℚ (A.cD τ)) → FinAlg (jetSet A a b S M n) := by
  intro X A a b S M n hX hM hE hT hC hJ hD
  classical
  obtain ⟨Ta, hTa, hTa'⟩ := GlobalTheory.Mem.Col2.JetEx.exists_finset_sdLat_reps X hX a
  obtain ⟨Tb, hTb, hTb'⟩ := GlobalTheory.Mem.Col2.JetEx.exists_finset_sdLat_reps X hX b
  let Z₀ : Set ℂ := ⋃ N ∈ (Ta : Set _), ⋃ N' ∈ (Tb : Set _), ⋃ c ∈ (M.divisors : Set ℕ),
    ⋃ G ∈ A.thInd S N N' c '' (divLat M (homAt S N N') : Set (HomE X.E a b)),
      ⋃ e ∈ {e : DVar X.Tau a b →₀ ℕ | e.degree ≤ n}, {(A.chiF a b N N')⁻¹ * derivAt0 G e}
  have hZ₀ : FinAlg Z₀ := by
    refine finAlg_biUnion Ta.finite_toSet fun N hN => finAlg_biUnion Tb.finite_toSet fun N' hN' =>
      finAlg_biUnion (Finset.finite_toSet _) fun c hc => ?_
    have hc' : c ∣ M := Nat.dvd_of_mem_divisors hc
    have hc0 : 0 < c := Nat.pos_of_mem_divisors hc
    refine finAlg_biUnion (finite_thInd A S N N' M c (hTa N hN) (hTb N' hN') hM hc0) ?_
    rintro _ ⟨x, hx, rfl⟩
    refine finAlg_biUnion (Finsupp.finite_of_degree_le n) fun e _ => finAlg_of_finite (Set.finite_singleton _) ?_
    rintro _ rfl
    exact hJ N N' c x ⟨hTa N hN, hTb N' hN', hc0, hc', hx⟩ e
  have h1 : FinAlg (Set.range A.cD) := finAlg_of_finite (Set.finite_range _) (by rintro _ ⟨τ, rfl⟩; exact hD τ)
  have h2 : FinAlg (⋃ τ ∈ (Set.univ : Set X.Tau), Set.range (X.embC A.σ₀ τ)) :=
    finAlg_biUnion Set.finite_univ fun τ _ => finAlg_range _
  refine ((hZ₀.union h1).union h2).closure.mono ?_
  set K₀ := Subfield.closure ((Z₀ ∪ Set.range A.cD) ∪ ⋃ τ ∈ (Set.univ : Set X.Tau), Set.range (X.embC A.σ₀ τ)) with hK₀
  have hemb : ∀ τ x, X.embC A.σ₀ τ x ∈ K₀ := fun τ x =>
    Subfield.subset_closure (Or.inr (Set.mem_biUnion (Set.mem_univ τ) ⟨x, rfl⟩))
  have hcD : ∀ τ, A.cD τ ∈ K₀ := fun τ => Subfield.subset_closure (Or.inl (Or.inr ⟨τ, rfl⟩))
  rintro _ ⟨N, N', c, x, e, hr, he, rfl⟩
  obtain ⟨N₀, hN₀, γ, rfl⟩ := hTa' N hr.1
  obtain ⟨N₀', hN₀', γ', rfl⟩ := hTb' N' hr.2.1
  obtain ⟨x₀, rfl⟩ : ∃ x₀ : HomE X.E a b, x = γ'.1.toLinearMap ∘ₗ x₀ ∘ₗ γ.1.symm.toLinearMap :=
    ⟨γ'.1.symm.toLinearMap ∘ₗ x ∘ₗ γ.1.toLinearMap, by ext v; simp⟩
  have hr₀ : InRange S M c N₀ N₀' x₀ :=
    ⟨hTa _ hN₀, hTb _ hN₀', hr.2.2.1, hr.2.2.2.1, (divLat_gmap_iff S M _ _ _ _ _).1 hr.2.2.2.2⟩
  have hth : A.thInd S (gmap γ.1 N₀) (gmap γ'.1 N₀') c (γ'.1.toLinearMap ∘ₗ x₀ ∘ₗ γ.1.symm.toLinearMap) =
      fun z => A.thInd S N₀ N₀' c x₀ (pullLin A γ.1 γ'.1 z) := funext (hT γ γ' N₀ N₀' c x₀ hr₀)
  have key : (A.chiF a b N₀ N₀')⁻¹ * derivAt0 (fun z => A.thInd S N₀ N₀' c x₀ (pullLin A γ.1 γ'.1 z)) e ∈ K₀ := by
    refine GlobalTheory.Mem.JetChain.derivAt0_comp_mem X.Tau a b n K₀ _ _ _ (indSmooth_of A a b S M hE N₀ N₀' c x₀ hr₀) ?_ ?_ e he
    · intro k τ i j
      show A.pullV a b γ.1 γ'.1 (coordX k) τ i j ∈ K₀
      unfold Amb.pullV
      refine sum_mem fun k' _ => sum_mem fun l _ => mul_mem (mul_mem (hemb _ _) ?_) (hemb _ _)
      unfold coordX
      split_ifs
      · exact one_mem _
      · exact zero_mem _
    · intro e' he'
      refine Subfield.subset_closure (Or.inl (Or.inl ?_))
      refine Set.mem_biUnion hN₀ (Set.mem_biUnion hN₀' (Set.mem_biUnion (x := c) ?_ (Set.mem_biUnion ⟨x₀, hr₀.2.2.2.2, rfl⟩
        (Set.mem_biUnion (x := e') he'.le rfl))))
      exact Finset.mem_coe.2 (Nat.mem_divisors.2 ⟨hr₀.2.2.2.1, hM.ne'⟩)
  show _ ∈ K₀
  rw [hth, hC γ γ' N₀ N₀' hr₀.1 hr₀.2.1, jetC, mul_inv, mul_assoc, mul_left_comm (A.chiF a b N₀ N₀')⁻¹]
  refine mul_mem (inv_mem (mul_mem (zpow_mem (prod_mem fun τ _ => hemb _ _) _) (zpow_mem (prod_mem fun τ _ => hemb _ _) _)))
    (mul_mem (prod_mem fun k _ => pow_mem (hcD _) _) key)

end GlobalTheory.Mem.Col2.JetFin

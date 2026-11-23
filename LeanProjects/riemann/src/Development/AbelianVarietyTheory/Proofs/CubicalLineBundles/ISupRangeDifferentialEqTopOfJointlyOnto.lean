import Mathlib
import Development.AbelianVarietyTheory.Definitions.CMLattices.ExistsIsThetaDegOfIsLocalModel
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsLinearOfIsMonHom
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.PolCountableAndTangentExt
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.PolFibreIdCompCancel
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsUniqueDifferentialMonHomLieBasisStatement
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.SubsingletonPrimeSpectrum
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsIsLieBasisBaseChange
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.LieCombBaseChange

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM

noncomputable section
namespace GlobalTheory.DiffSpan

theorem eq_top_of_countable {V : Type} [AddCommGroup V] [Module ℂ V] (S : Submodule ℂ V) {Λ : Set V}
    (hΛ : Λ.Countable) (h : ∀ z, ∃ s ∈ S, z - s ∈ Λ) : S = ⊤ := by
  by_contra hS
  obtain ⟨ℓ, hℓ, hker⟩ := S.exists_le_ker_of_lt_top (lt_top_iff_ne_top.2 hS)
  have : Uncountable ℂ := Complex.ofReal_injective.uncountable
  refine Set.not_countable_univ (α := ℂ) ((hΛ.image ℓ).mono fun c _ => ?_)
  obtain ⟨z, rfl⟩ := LinearMap.surjective_of_ne_zero hℓ c
  obtain ⟨s, hs, hz⟩ := h z
  exact ⟨_, hz, by rw [map_sub, (hker hs : ℓ s = 0), sub_zero]⟩

theorem eq_top_of_span_image {K L : Type} [Field K] [Field L] (σ : K →+* L) {g : ℕ} (N : Submodule K (Fin g → K))
    (h : Submodule.span L ((fun m k => σ (m k)) '' (N : Set (Fin g → K))) = ⊤) : N = ⊤ := by
  classical
  by_contra hN
  obtain ⟨ℓ, hℓ, hker⟩ := N.exists_le_ker_of_lt_top (lt_top_iff_ne_top.2 hN)
  let ℓ' : (Fin g → L) →ₗ[L] L := Fintype.linearCombination L fun k => σ (ℓ (Pi.single k 1))
  have e : ∀ m, ℓ' (fun k => σ (m k)) = σ (ℓ m) := fun m => by
    conv_rhs => rw [pi_eq_sum_univ' m]
    simp [ℓ', Fintype.linearCombination_apply]
  have h0 : ∀ c, ℓ' c = 0 := fun c => by
    have : Submodule.span L ((fun m k => σ (m k)) '' (N : Set (Fin g → K))) ≤ LinearMap.ker ℓ' := by
      rw [Submodule.span_le]
      rintro _ ⟨m, hm, rfl⟩
      exact (e m).trans (by rw [(hker hm : ℓ m = 0), map_zero])
    exact this (h ▸ Submodule.mem_top)
  exact hℓ (LinearMap.ext fun m => σ.injective (by rw [← e, h0]; simp))

section Unif

variable {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g : ℕ} (u : HolUnif A L g)

theorem ex_zero : u.ex 0 = 1 := (u.ker 0).2 u.Λ.zero_mem

theorem ex_sum : ∀ {n : ℕ} (z : Fin n → Fin g → ℂ), u.ex (∑ m, z m) = (List.ofFn fun m => u.ex (z m)).prod
  | 0, z => by simpa using ex_zero u
  | n + 1, z => by rw [Fin.sum_univ_succ, u.ex_add, ex_sum, List.ofFn_succ, List.prod_cons]

theorem sub_mem_of_ex_eq {z w : Fin g → ℂ} (h : u.ex z = u.ex w) : z - w ∈ u.Λ := by
  have e := u.ex_add (z - w) w
  rw [sub_add_cancel, h] at e
  exact (u.ker _).1 (mul_eq_right.1 e.symm)

theorem surjective_of_isLieBasis (hd : ∀ v, IsTangent v → ∃! w, u.IsDiff w v)
    (he : ∀ w, ∃! v, IsTangent v ∧ u.IsDiff w v) {n : ℕ} {v : Fin n → (epsR ℂ ⟶ A)} (hv : IsLieBasis v)
    {W : Fin n → Fin g → ℂ} (hW : ∀ i, u.IsDiff (W i) (v i)) :
    Function.Surjective (Fintype.linearCombination ℂ W) := fun w => by
  obtain ⟨x, ⟨hx, dx⟩, -⟩ := he w
  obtain ⟨c, hc, -⟩ := hv.2 x hx
  exact ⟨c, (hd x hx).unique (UnifDifferential.isDiff_of_isLieComb A L g n u W v c x hv.1 hW hc) dx⟩

end Unif

theorem exists_fibre (hU : ThetaUnifAV) (hB : Out.PolBaseChangeSt) {K : Type} [Field K] (σ : K →+* ℂ)
    (P : Out.PolAV (Sp K)) {v : Fin P.g → (epsR K ⟶ P.A)} (hv : IsLieBasis v) :
    ∃ (Q : Out.PolAV (Sp ℂ)) (ψ : Q.A.left ⟶ P.A.left) (v' : Fin P.g → (epsR ℂ ⟶ Q.A)) (u : HolUnif Q.A Q.L Q.g)
      (W : Fin P.g → Fin Q.g → ℂ), IsPolFibre σ P Q ψ ∧ (∀ i, IsTangent (v' i)) ∧ (∀ i, IsVecOver σ ψ (v i) (v' i)) ∧
      (∀ x, IsTangent x → ∃! w, u.IsDiff w x) ∧ (∀ w, ∃! x, IsTangent x ∧ u.IsDiff w x) ∧
      (∀ i, u.IsDiff (W i) (v' i)) ∧ Function.Bijective (Fintype.linearCombination ℂ W) := by
  obtain ⟨Q, ψ, hQ⟩ := exists_isPolFibre hB σ P
  have := P.isAb.comm
  have := Q.isAb.comm
  have := P.smoothDim
  obtain ⟨v', hv', ho⟩ := exists_isLieBasis_baseChange K ℂ σ P.A Q.A ψ hQ.2.1
    (SmoothOfRelativeDimension.smooth P.g _) _ v hv
  obtain ⟨rig, hrig⟩ := Q.rigid
  obtain ⟨u, -, -, -, -, -, hd, he, -⟩ := hU Q rig hrig
  choose W hW using fun i => (hd _ (hv'.1 i)).exists
  have hs := surjective_of_isLieBasis u hd he hv' hW
  exact ⟨Q, ψ, v', u, W, hQ, hv'.1, ho, hd, he, hW,
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (by simp [hQ.1])).2 hs, hs⟩

theorem exists_prod_of_ontoAt {R : Type} [CommRing R] {s : R →+* ℂ} {I : Type} {B : I → Over (Sp R)} {A : Over (Sp R)}
    [GrpObj A] {B' : I → Over (Sp ℂ)} {A' : Over (Sp ℂ)} [GrpObj A'] {f : ∀ i, B i ⟶ A} {f' : ∀ i, B' i ⟶ A'}
    {φ : A'.left ⟶ A.left} {ψ : ∀ i, (B' i).left ⟶ (B i).left} (hφ : IsGrpPullback A' A (spMap s) φ)
    (hψ : ∀ i, IsPullback (ψ i) (B' i).hom (B i).hom (spMap s)) (hf : ∀ i, (f' i).left ≫ φ = ψ i ≫ (f i).left)
    (h : OntoAt f (spMap s)) (y : 𝟙_ (Over (Sp ℂ)) ⟶ A') :
    ∃ (n : ℕ) (i : Fin n → I) (x : ∀ m, 𝟙_ (Over (Sp ℂ)) ⟶ B' (i m)),
      y = (List.ofFn fun m => x m ≫ f' (i m)).prod := by
  obtain ⟨n, i, x, e⟩ := h (Over.homMk (y.left ≫ φ) (by
    rw [Category.assoc, hφ.1.w, ← Category.assoc, Over.w y]
    exact Category.id_comp _))
  have w : ∀ m, (x m).left ≫ (B (i m)).hom = 𝟙 _ ≫ spMap s := fun m =>
    (Over.w (x m)).trans (Category.id_comp _).symm
  let x' : ∀ m, 𝟙_ (Over (Sp ℂ)) ⟶ B' (i m) := fun m =>
    Over.homMk ((hψ _).lift _ _ (w m)) ((hψ _).lift_snd _ _ (w m))
  refine ⟨n, i, x', Over.OverMorphism.ext (hφ.1.hom_ext ?_ (by rw [Over.w, Over.w]))⟩
  refine Eq.trans ?_ (LieCombBaseChange.prod_left_comp hφ (T := Over.mk (spMap s)) (T' := 𝟙_ (Over (Sp ℂ))) (𝟙 _) rfl
    (fun m => x m ≫ f (i m)) _ fun m => ?_).symm
  · rw [← e]
    exact (Category.id_comp _).symm
  · rw [Over.comp_left, Category.assoc, hf, ← Category.assoc, Category.id_comp, Over.comp_left]
    exact congrArg (· ≫ (f (i m)).left) ((hψ _).lift_fst _ _ (w m))

theorem iSup_range_diff_eq_top : ThetaUnifAV → Out.Laws → ∀ (K : Type) [Field K] [NumberField K] (P : Out.PolAV (Sp (𝓞 K))) (F : GenFib P) (σ : K →+* ℂ) (I : Type) (Q : I → Out.PolAV (Sp (𝓞 K))) (FQ : ∀ i, GenFib (Q i)) (f : ∀ i, (Q i).A ⟶ P.A) (M : ∀ i, (Fin (FQ i).P₀.g → K) →ₗ[K] (Fin F.P₀.g → K)), Finite I → (∀ i, IsMonHom (f i)) → (∀ i, (FQ i).IsDiffOf F (f i) (M i)) → OntoAt f (spMap (σ.comp (algebraMap (𝓞 K) K))) → ⨆ i, LinearMap.range (M i) = ⊤ := by
  intro hU hL K _ _ P F σ I Q FQ f M _ hf hM ho
  obtain ⟨P', ψ, v, u, W, hP, tv, ov, hd, he, hW, bW⟩ := exists_fibre hU hL.polBaseChange σ F.P₀ F.basis
  choose Q' χ t r V hQ tt ot _ _ hV bV using fun i => exists_fibre hU hL.polBaseChange σ (FQ i).P₀ (FQ i).basis
  choose f₀ hf₀ e₀ d₀ using fun i => (T.existsUnique_differential_monHom_lieBasis K (Q i) (FQ i) P F (f i) (hf i)).2
  choose f' hf' e' using fun i => HomDescent.exists_isMonHom_pull (hQ i).2.1 hP.2.1 (f₀ i)
  choose Φ hΦ _ dΦ _ using fun i => HomLinear.exists_linear_of_isMonHom (Q' i).A P'.A (Q' i).isAb P'.isAb (Q' i).L P'.L
    _ _ (r i) u hd he (f' i) (hf' i)
  refine eq_top_of_span_image σ _ ?_
  set S := Submodule.span ℂ ((fun m k => σ (m k)) '' ((⨆ i, LinearMap.range (M i) : Submodule K _) : Set (Fin F.P₀.g → K)))
  have hS : ∀ i z, Φ i z ∈ S.map (Fintype.linearCombination ℂ W) := fun i z => by
    obtain ⟨a, rfl⟩ := (bV i).2 z
    rw [Fintype.linearCombination_apply, map_sum]
    refine Submodule.sum_mem _ fun j _ => ?_
    rw [map_smul]
    refine Submodule.smul_mem _ _ ?_
    obtain ⟨c, hc, -⟩ := (FQ i).basis.2 _ ((FQ i).basis.1 j)
    have h₁ := (lieComb_baseChange K ℂ σ _ _ ψ hP.2.1 _ _ _ _ v (t i j ≫ f' i) ov (d₀ i _ (hM i) c _ hc)).1 (by
      rw [Over.comp_left, Over.comp_left, Category.assoc, e', ← Category.assoc, ot i j, Category.assoc])
    obtain ⟨h₂, h₃⟩ := dΦ i _ _ (tt i j) (hV i j)
    exact ⟨fun k => σ (M i c k), Submodule.subset_span ⟨M i c, Submodule.mem_iSup_of_mem i ⟨c, rfl⟩, rfl⟩,
      (hd _ h₂).unique (UnifDifferential.isDiff_of_isLieComb _ _ _ _ u W v _ _ tv hW h₁) h₃⟩
  have htop : S.map (Fintype.linearCombination ℂ W) = ⊤ := by
    have := u.discrete
    refine eq_top_of_countable _ (Λ := u.Λ) (countable_of_Lindelof_of_discrete (X := u.Λ)) fun z => ?_
    obtain ⟨n, i, x, e⟩ := exists_prod_of_ontoAt (f' := f') (PolFibre.comp F.fib hP).2.1
      (fun i => (PolFibre.comp (FQ i).fib (hQ i)).2.1.1)
      (fun i => by rw [← Category.assoc, e', Category.assoc, e₀, Category.assoc]) ho (u.ex z)
    choose w hw using fun m => (r (i m)).ex_onto (x m)
    refine ⟨∑ m, Φ (i m) (w m), Submodule.sum_mem _ fun m _ => hS _ _, sub_mem_of_ex_eq u ?_⟩
    simp only [ex_sum, hΦ, hw, e]
  exact Submodule.map_injective_of_injective bW.1
    (htop.trans ((Submodule.map_top _).trans (LinearMap.range_eq_top.2 bW.2)).symm)

end GlobalTheory.DiffSpan

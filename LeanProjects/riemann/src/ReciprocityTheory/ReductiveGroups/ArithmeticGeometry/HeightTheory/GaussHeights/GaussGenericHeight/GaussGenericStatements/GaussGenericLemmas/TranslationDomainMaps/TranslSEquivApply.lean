import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.HtLeafSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.GaussHeights.GaussGenericHeight.GaussGenericStatements.GaussGenericLemmas.TranslationDomainMaps.MapDomainMemOfDvd

namespace ReciprocityTheory.ChartRestriction.G.T0

namespace GaussGen

open MvPolynomial NumberField BlockPoly

section Img

variable {Ω : Type} [Field Ω] {D N : ℕ}

noncomputable def Pimg (j₀ : Fin (N + 1)) (x : Fin N → Ω) (p : TVar D N) :
    MvPolynomial (SVar D N) Ω :=
  Fin.succAboveCases (α := fun _ => MvPolynomial (SVar D N) Ω) j₀
      (if p.1 = 0 then MvPolynomial.X (Sum.inl ())
        else -∑ k, MvPolynomial.X (Sum.inr (p.1, k)) * MvPolynomial.C (x k))
      (fun k => MvPolynomial.X (Sum.inr (p.1, k))) p.2

theorem Pimg_self (j₀ : Fin (N + 1)) (x : Fin N → Ω) (i : Fin (D + 1)) :
    Pimg j₀ x (i, j₀) =
      if i = 0 then X (Sum.inl ()) else -∑ k, X (Sum.inr (i, k)) * C (x k) := by
  unfold Pimg
  exact Fin.insertNth_apply_same (α := fun _ => MvPolynomial (SVar D N) Ω) j₀ _ _

theorem Pimg_succAbove (j₀ : Fin (N + 1)) (x : Fin N → Ω) (i : Fin (D + 1)) (k : Fin N) :
    Pimg j₀ x (i, j₀.succAbove k) = X (Sum.inr (i, k)) := by
  unfold Pimg
  exact Fin.insertNth_apply_succAbove (α := fun _ => MvPolynomial (SVar D N) Ω) j₀ _ _ k

theorem sHom_eq {K : Type} [Field K] [Algebra K Ω] (j₀ : Fin (N + 1)) (x : Fin N → Ω)
    (y : MvPolynomial (TVar D N) K) :
    sHom j₀ x y = algebraMap (MvPolynomial (SVar D N) Ω) (OmS Ω D N) (aeval (Pimg j₀ x) y) := by
  show aeval (sImg j₀ x) y = _
  rw [← MvPolynomial.aeval_algebraMap_apply]
  rfl

def blk : SVar D N → Fin (D + 1)
  | Sum.inl _ => 0
  | Sum.inr q => q.1

def col (j₀ : Fin (N + 1)) : SVar D N → Fin (N + 1)
  | Sum.inl _ => j₀
  | Sum.inr q => j₀.succAbove q.2

def cS (b : Fin (D + 1)) (μ : Ω) : SVar D N → Ω := fun s => if blk s = b then μ else 1

theorem cS_ne_zero {μ : Ω} (hμ : μ ≠ 0) (b : Fin (D + 1)) (s : SVar D N) : cS b μ s ≠ 0 := by
  unfold cS
  split_ifs
  · exact hμ
  · exact one_ne_zero

private theorem diag_cS_Pimg (j₀ : Fin (N + 1)) (x : Fin N → Ω) (b : Fin (D + 1)) (μ : Ω)
    (t : TVar D N) :
    diag (cS b μ) (Pimg j₀ x t) = C (if t.1 = b then μ else 1) * Pimg j₀ x t := by
  obtain ⟨i, j⟩ := t
  have hC : ∀ a : Ω, diag (cS (N := N) b μ) (C a) = C a := fun a => by simp [diag]
  rcases Fin.eq_self_or_eq_succAbove j₀ j with rfl | ⟨k, rfl⟩
  · rw [Pimg_self]
    by_cases hi : i = 0
    · subst hi
      rw [if_pos rfl, diag_X]
      rfl
    · rw [if_neg hi, map_neg, map_sum, mul_neg, Finset.mul_sum]
      congr 1
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [map_mul, diag_X, hC, mul_assoc]
      rfl
  · rw [Pimg_succAbove, diag_X]
    rfl

theorem lift_scale {K : Type} [Field K] [CharZero K] [Algebra K Ω] (j₀ : Fin (N + 1))
    (x : Fin N → Ω) (b : Fin (D + 1)) (t : TVar D N) :
    diag (cS b (2 : Ω)) (Pimg j₀ x t) = aeval (Pimg j₀ x) (diag (cb b (2 : K)) (X t)) := by
  rw [diag_cS_Pimg, diag_X, map_mul, aeval_X, aeval_C]
  congr 1
  obtain ⟨i, j⟩ := t
  show C (if i = b then (2 : Ω) else 1) = algebraMap K _ (if i = b then (2 : K) else 1)
  split_ifs
  · rw [MvPolynomial.algebraMap_apply]
    congr 1
    exact (map_ofNat (algebraMap K Ω) 2).symm
  · simp

def eS (e : Equiv.Perm (Fin (D + 1))) : SVar D N ≃ SVar D N :=
  Equiv.sumCongr (Equiv.refl Unit) (Equiv.prodCongr e (Equiv.refl (Fin N)))

theorem lift_swap {K : Type} [Field K] [Algebra K Ω] (j₀ : Fin (N + 1)) (x : Fin N → Ω)
    (e : Equiv.Perm (Fin (D + 1))) (he : e 0 = 0) (t : TVar D N) :
    rename (eS e) (Pimg j₀ x t) = aeval (Pimg j₀ x) (rename (eT e) (X t) : MvPolynomial _ K) := by
  obtain ⟨i, j⟩ := t
  rw [rename_X, aeval_X]
  show rename (eS e) (Pimg j₀ x (i, j)) = Pimg j₀ x (e i, j)
  rcases Fin.eq_self_or_eq_succAbove j₀ j with rfl | ⟨k, rfl⟩
  · rw [Pimg_self, Pimg_self]
    by_cases hi : i = 0
    · subst hi
      simp [he, eS]
    · have hei : e i ≠ 0 := fun h' => hi (e.injective (h'.trans he.symm))
      simp [hi, hei, eS, map_sum, map_neg]
  · rw [Pimg_succAbove, Pimg_succAbove, rename_X]
    rfl

noncomputable def translS (j₀ : Fin (N + 1)) (a : Fin (N + 1) → Ω) :
    MvPolynomial (SVar D N) Ω →ₐ[Ω] MvPolynomial (SVar D N) Ω :=
  aeval fun s => if blk s = 0 then X s + C (a (col j₀ s)) else X s

theorem translS_X (j₀ : Fin (N + 1)) (a : Fin (N + 1) → Ω) (s : SVar D N) :
    translS j₀ a (X s) = if blk s = 0 then X s + C (a (col j₀ s)) else X s := by
  show aeval _ (X s) = _
  rw [aeval_X]

noncomputable def translSEquiv (j₀ : Fin (N + 1)) (a : Fin (N + 1) → Ω) :
    MvPolynomial (SVar D N) Ω ≃ₐ[Ω] MvPolynomial (SVar D N) Ω :=
  AlgEquiv.ofAlgHom (translS j₀ a) (translS j₀ (-a))
    (algHom_ext fun s => by by_cases h : blk s = 0 <;> simp [translS_X, h])
    (algHom_ext fun s => by by_cases h : blk s = 0 <;> simp [translS_X, h])

@[simp] theorem translSEquiv_apply (j₀ : Fin (N + 1)) (a : Fin (N + 1) → Ω)
    (g : MvPolynomial (SVar D N) Ω) : translSEquiv j₀ a g = translS j₀ a g := rfl

theorem lift_transl {K : Type} [Field K] [Algebra K Ω] (j₀ : Fin (N + 1)) (x : Fin N → Ω)
    (a : Fin (N + 1) → K) (t : TVar D N) :
    translS j₀ (fun j => algebraMap K Ω (a j)) (Pimg j₀ x t) =
      aeval (Pimg j₀ x) (transl a (X t)) := by
  obtain ⟨i, j⟩ := t
  rw [transl_X]
  rcases Fin.eq_self_or_eq_succAbove j₀ j with rfl | ⟨k, rfl⟩ <;> by_cases hi : i = 0
  · subst hi
    simp [Pimg_self, translS, blk, col, MvPolynomial.algebraMap_apply]
  · simp [Pimg_self, translS, blk, col, hi, map_sum, map_neg]
  · subst hi
    simp [Pimg_succAbove, translS, blk, col, MvPolynomial.algebraMap_apply]
  · simp [Pimg_succAbove, translS, blk, col, hi]

end Img

section Stab

variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι]
  {Ω : ι → Type} [∀ c, Field (Ω c)] [∀ c, Algebra K (Ω c)]
  {WT : Type} [AddCommGroup WT]
  {A : ι → Type} [∀ c, CommRing (A c)] [∀ c, Algebra (Ω c) (A c)] [∀ c, Algebra K (A c)]
  [∀ c, Algebra (𝓞 K) (A c)]
  (𝒜 : (c : ι) → WT → Submodule (Ω c) (A c)) (d : Data K ι Ω WT A)

theorem comap_eq (hx1 : LeafSt.PlaceTrivialOrPositive 𝒜 d) (hx2 : LeafSt.AdmissibleValuationPrimeUnique 𝒜 d)
    (hd : d.AxH 𝒜) (h : d.S1) (c : ι) (p : Ideal (KTp K d.D d.N)) (hp : p ∈ d.HtOne)
    (w : AddValuation (OmS (Ω c) d.D d.N) (WithTop ℤ)) (hw : w ∈ d.GoodP c p)
    (σ : KTp K d.D d.N ≃ₐ[K] KTp K d.D d.N)
    (τ : MvPolynomial (SVar d.D d.N) (Ω c) ≃ₐ[Ω c] MvPolynomial (SVar d.D d.N) (Ω c))
    (hc : ∀ t, τ (Pimg (d.jc c) (d.x c) t) = aeval (Pimg (d.jc c) (d.x c)) (σ (X t))) :
    p.comap σ = p := by
  let e : OmS (Ω c) d.D d.N ≃+* OmS (Ω c) d.D d.N :=
    IsFractionRing.ringEquivOfRingEquiv τ.toRingEquiv
  have he : ∀ r, e (algebraMap (MvPolynomial (SVar d.D d.N) (Ω c)) (OmS (Ω c) d.D d.N) r) =
      algebraMap (MvPolynomial (SVar d.D d.N) (Ω c)) (OmS (Ω c) d.D d.N) (τ r) :=
    fun r => IsFractionRing.ringEquivOfRingEquiv_algebraMap τ.toRingEquiv r
  have hτ : ∀ y : KTp K d.D d.N, τ (aeval (Pimg (d.jc c) (d.x c)) y) =
      aeval (Pimg (d.jc c) (d.x c)) (σ y) := by
    intro y
    have hcomp : ((τ : MvPolynomial (SVar d.D d.N) (Ω c) →ₐ[Ω c] _).restrictScalars K).comp
        (aeval (Pimg (d.jc c) (d.x c))) =
        (aeval (Pimg (d.jc c) (d.x c))).comp (σ : KTp K d.D d.N →ₐ[K] KTp K d.D d.N) := by
      apply MvPolynomial.algHom_ext
      intro t
      show τ (aeval (Pimg (d.jc c) (d.x c)) (X t)) = aeval (Pimg (d.jc c) (d.x c)) (σ (X t))
      rw [aeval_X]
      exact hc t
    exact DFunLike.congr_fun hcomp y
  have hsH : ∀ y, d.sH c y = algebraMap (MvPolynomial (SVar d.D d.N) (Ω c)) (OmS (Ω c) d.D d.N)
      (aeval (Pimg (d.jc c) (d.x c)) y) := fun y => sHom_eq (d.jc c) (d.x c) y
  have hw' : ∀ y, (w.comap (e : OmS (Ω c) d.D d.N →+* OmS (Ω c) d.D d.N)) (d.sH c y) =
      w (d.sH c (σ y)) := by
    intro y
    show w (e (d.sH c y)) = w (d.sH c (σ y))
    rw [hsH, hsH, he, hτ]
  have hWres : d.Wres c (w.comap (e : OmS (Ω c) d.D d.N →+* OmS (Ω c) d.D d.N)) = d.Wres c w := by
    refine AddValuation.ext fun a => ?_
    show w (e (algebraMap (Ω c) (OmS (Ω c) d.D d.N) a)) = w (algebraMap (Ω c) (OmS (Ω c) d.D d.N) a)
    rw [IsScalarTower.algebraMap_apply (Ω c) (MvPolynomial (SVar d.D d.N) (Ω c))
      (OmS (Ω c) d.D d.N), he, AlgEquiv.commutes]
  have hpσ : p.comap σ ∈ d.HtOne := by
    refine ⟨?_, ?_⟩
    · have := hp.1
      exact Ideal.comap_isPrime σ p
    · exact (RingEquiv.height_comap (σ : KTp K d.D d.N ≃+* KTp K d.D d.N) p).trans hp.2
  have hmem : w.comap (e : OmS (Ω c) d.D d.N →+* OmS (Ω c) d.D d.N) ∈ d.GoodP c (p.comap σ) := by
    obtain ⟨⟨⟨hfin, π, hπ⟩, hov⟩, a, ha, hwa⟩ := hw
    refine ⟨⟨⟨fun z hz => ?_, e.symm π, ?_⟩, fun y => ?_⟩, a, ha, ?_⟩
    · show w (e z) ≠ ⊤
      exact hfin _ ((map_ne_zero e).mpr hz)
    · show w (e (e.symm π)) = 1
      rw [RingEquiv.apply_symm_apply]
      exact hπ
    · rw [hw', Ideal.mem_comap]
      exact hov (σ y)
    · rw [hWres]
      exact hwa
  rcases hx1 hd h c p hp w hw.1 with h0 | ⟨hadm, htriv, -⟩
  · obtain ⟨a, ha, hwa⟩ := hw.2
    exact absurd (h0 a ha) hwa
  · have m1 : p.comap σ ∈ {q | q ∈ d.HtOne ∧ ∃ w₁ ∈ d.GoodP c q, d.Wres c w₁ = d.Wres c w} :=
      ⟨hpσ, _, hmem, hWres⟩
    have m2 : p ∈ {q | q ∈ d.HtOne ∧ ∃ w₁ ∈ d.GoodP c q, d.Wres c w₁ = d.Wres c w} :=
      ⟨hp, w, hw, rfl⟩
    exact hx2 hd h c (d.Wres c w) hadm htriv m1 m2

end Stab

end GaussGen

end ReciprocityTheory.ChartRestriction.G.T0

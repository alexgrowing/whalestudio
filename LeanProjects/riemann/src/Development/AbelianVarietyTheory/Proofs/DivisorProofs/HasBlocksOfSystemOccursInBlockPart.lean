import Development.AbelianVarietyTheory.Definitions.Divisors.HasBlockOfOccurs
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ChebotarevDegreeOneIffCheb
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeCrystallineLattices

set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain Formalism.L2.DIV GlobalTheory.ExpFrame Formalism.CohomologicalDescent.DepthNonnegative Formalism.CohomologicalDescent.LogSmallConstantBounds Formalism.CohomologicalDescent.ShortWeightBounds Formalism.CohomologicalDescent.LD Formalism.RankGapBounds.FormsTensorLocalization

namespace GlobalTheory.OccBlock

open Module Module.End

section Gen

variable {L V J : Type} [Field L] [DecidableEq L] [AddCommGroup V] [Module L V]

def jointGen (T : J → End L V) (y : J → L) : Submodule L V := ⨅ j, (T j).maxGenEigenspace (y j)

theorem mem_iSup_filter (T : J → End L V) (p : (J → L) → Submodule L V) (hp : ∀ y, p y ≤ jointGen T y) {θ : J → L} {f : V}
    (hf : ∀ j, T j f = θ j • f) (Y : Finset (J → L)) (j : J) (hY : f ∈ ⨆ y ∈ Y, p y) :
    f ∈ ⨆ y ∈ Y.filter (fun y => y j = θ j), p y := by
  have hsplit : (⨆ y ∈ Y, p y) ≤ (⨆ y ∈ Y.filter (fun y => y j = θ j), p y) ⊔
      (⨆ y ∈ Y.filter (fun y => y j ≠ θ j), p y) := by
    refine iSup₂_le fun y hy => ?_
    by_cases h : y j = θ j
    · exact le_sup_of_le_left (le_biSup p (Finset.mem_filter.2 ⟨hy, h⟩))
    · exact le_sup_of_le_right (le_biSup p (Finset.mem_filter.2 ⟨hy, h⟩))
  obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.1 (hsplit hY)
  have hA : (⨆ y ∈ Y.filter (fun y => y j = θ j), p y) ≤ (T j).maxGenEigenspace (θ j) := by
    refine iSup₂_le fun y hy => ?_
    have hyj := (Finset.mem_filter.1 hy).2
    calc p y ≤ jointGen T y := hp y
      _ ≤ (T j).maxGenEigenspace (y j) := iInf_le (fun j => (T j).maxGenEigenspace (y j)) j
      _ = (T j).maxGenEigenspace (θ j) := by rw [hyj]
  have hB : (⨆ y ∈ Y.filter (fun y => y j ≠ θ j), p y) ≤ ⨆ (μ : L) (_ : μ ≠ θ j), (T j).maxGenEigenspace μ := by
    refine iSup₂_le fun y hy => ?_
    calc p y ≤ jointGen T y := hp y
      _ ≤ (T j).maxGenEigenspace (y j) := iInf_le (fun j => (T j).maxGenEigenspace (y j)) j
      _ ≤ _ := le_biSup (fun μ => (T j).maxGenEigenspace μ) (show y j ∈ {μ | μ ≠ θ j} from (Finset.mem_filter.1 hy).2)
  have hfθ : f ∈ (T j).maxGenEigenspace (θ j) := by
    rw [mem_maxGenEigenspace]
    exact ⟨1, by simp [hf j]⟩
  have hb0 : b = 0 := by
    have hb1 : b ∈ (T j).maxGenEigenspace (θ j) := by
      have hbe : b = f - a := by rw [← hab]; abel
      rw [hbe]
      exact Submodule.sub_mem _ hfθ (hA ha)
    exact (Submodule.disjoint_def.1 ((Module.End.independent_maxGenEigenspace (T j)) (θ j))) b hb1 (hB hb)
  rw [← hab, hb0, add_zero]
  exact ha

theorem mem_of_mem_iSup_finset (T : J → End L V) (p : (J → L) → Submodule L V) (hp : ∀ y, p y ≤ jointGen T y)
    {θ : J → L} {f : V} (hf : ∀ j, T j f = θ j • f) (Y : Finset (J → L)) (hY : f ∈ ⨆ y ∈ Y, p y) : f ∈ p θ := by
  induction Y using Finset.strongInduction with
  | H Y ih =>
    by_cases h : ∃ y ∈ Y, y ≠ θ
    · obtain ⟨y0, hy0, hne⟩ := h
      obtain ⟨j, hj⟩ := Function.ne_iff.1 hne
      exact ih _ (Finset.filter_ssubset.2 ⟨y0, hy0, hj⟩) (mem_iSup_filter T p hp hf Y j hY)
    · push_neg at h
      exact (iSup₂_le fun y hy => by rw [h y hy] : (⨆ y ∈ Y, p y) ≤ p θ) hY

end Gen

section Read

variable {l : ℕ} [Fact l.Prime] {ι : Type} [DecidableEq ι] {N : ℕ} (F : Frame l ι N) (lam : ι → ℕ → ℕ)

def heckeQ (i : F.I) : End (PadicAlgCl l) (F.G → NablaT (PadicAlgCl l) N lam) where
  toFun h g := F.emb (F.cst i) • ∑ s ∈ F.tr i, h (g * s)
  map_add' h h' := by
    funext g
    simp [Finset.sum_add_distrib, smul_add]
  map_smul' c h := by
    funext g
    simp only [Pi.smul_apply, Finset.smul_sum, RingHom.id_apply]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [smul_smul, smul_smul, mul_comm]

variable {F lam} {K : Type} [Field K] [NumberField K] [StarRing K] {G0 : Type} [Group G0] [Fintype G0] {Pl0 : Type}
  {B : BlockDat K G0 Pl0} {w : HeightOneSpectrum (𝓞 K)}

theorem rd_pow (R : Reads F lam B w) (i : F.I) (a : K) (k : ℕ) (v : B.S.Forms) :
    R.rd (((B.op (R.ix i) - a • (1 : End K B.S.Forms)) ^ k) v) =
      ((heckeQ F lam i - R.e0 a • (1 : End (PadicAlgCl l) (F.G → NablaT (PadicAlgCl l) N lam))) ^ k) (R.rd v) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', pow_succ', Module.End.mul_apply, Module.End.mul_apply, ← ih]
    funext g
    simp [map_sub, map_smulₛₗ, R.hecke, heckeQ]

end Read

theorem hasBlock_of_occurs : ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (G0 : Type) [Group G0] [Fintype G0] (Pl0 : Type)
    (B : BlockDat K G0 Pl0) (w : HeightOneSpectrum (𝓞 K)) (l : ℕ) [Fact l.Prime] (ι : Type) [DecidableEq ι] (N : ℕ) (F : Frame l ι N)
    (lam : ι → ℕ → ℕ) (R : Reads F lam B w) (Z : Submodule K B.S.Forms), (∀ P, B.op (P, 0) = 1) →
    Z ≤ B.ZH → ∀ θ, R.Occurs Z θ → R.HasBlock θ ∧ F.IsEig lam θ := by
  intro K _ _ _ G0 _ _ Pl0 B w l _ ι _ N F lam R Z hop hZ θ hocc
  obtain ⟨f, hfspan, hfe⟩ := hocc
  refine ⟨?_, ⟨f, hfe⟩⟩
  classical
  let S : Set (F.I → PadicAlgCl l) :=
    {y | ∃ x : B.Pl × ℕ → K, (∀ P, x (P, 0) = 1) ∧ Formalism.L2.Col.HasBlocks B.n B.q B.t B.bl x ∧ ∀ i, y i = R.e0 (x (R.ix i))}
  let p : (F.I → PadicAlgCl l) → Submodule (PadicAlgCl l) (F.G → NablaT (PadicAlgCl l) N lam) :=
    fun y => ⨆ (_ : y ∈ S), jointGen (heckeQ F lam) y
  have hp : ∀ y, p y ≤ jointGen (heckeQ F lam) y := fun y => iSup_le fun _ => le_rfl
  have key : B.ZH ≤ (⨆ y, p y).comap R.rd := by
    rw [BlockDat.ZH, Formalism.L2.Col.blockSum, Formalism.L2.Col.eigSum]
    refine iSup₂_le fun x hx => ?_
    intro v hv
    rw [Submodule.mem_comap]
    by_cases hv0 : v = 0
    · rw [hv0, map_zero]
      exact Submodule.zero_mem _
    have hx1 : ∀ P, x (P, 0) = 1 := fun P =>
      GlobalTheory.ExpFrame.eq_one_of_occurs (op := B.op) ((Submodule.ne_bot_iff _).2 ⟨v, hv, hv0⟩) (hop P)
    refine Submodule.mem_iSup_of_mem (fun i => R.e0 (x (R.ix i))) ?_
    refine Submodule.mem_iSup_of_mem (show (fun i => R.e0 (x (R.ix i))) ∈ S from ⟨x, hx1, hx, fun i => rfl⟩) ?_
    rw [jointGen, Submodule.mem_iInf]
    intro i
    have hv' := Formalism.L2.Col.eigAt_le B.op x (R.ix i) hv
    rw [mem_maxGenEigenspace] at hv' ⊢
    obtain ⟨k, hk⟩ := hv'
    exact ⟨k, by rw [← rd_pow, hk, map_zero]⟩
  have hspan : Submodule.span (PadicAlgCl l) (R.rd '' Z) ≤ ⨆ y, p y := by
    rw [Submodule.span_le]
    rintro _ ⟨z, hz, rfl⟩
    exact key (hZ hz)
  obtain ⟨Y, hY⟩ := Submodule.mem_iSup_iff_exists_finset.1 (hspan hfspan)
  have hf : ∀ i, heckeQ F lam i f = θ i • f := fun i => by
    funext g
    exact hfe.2.2 i g
  have hθ := mem_of_mem_iSup_finset (heckeQ F lam) p hp hf Y hY
  by_cases hθS : θ ∈ S
  · exact hθS
  · exfalso
    have h0 : p θ = ⊥ := by simp [p, hθS]
    rw [h0, Submodule.mem_bot] at hθ
    exact hfe.1 hθ

end GlobalTheory.OccBlock

end

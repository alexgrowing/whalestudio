import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.SelfDualAt
import Formalism.LocalToGlobal.HermitianForms.TiedStep
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.DualLatticeLocalCharacterization
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsLatticeVectorApproxAllFinitePlaces
open Formalism.BasicNotions Formalism.UG Formalism.L2.Forms NumberField IsDedekindDomain Matrix GlobalTheory.St.G
open scoped TensorProduct

namespace GlobalTheory.St.G.GlobIdx

theorem prod_relIndex_dvd {G ι : Type} [AddCommGroup G] {M : ι → Type} [∀ i, AddCommGroup (M i)]
    (B A : AddSubgroup G) (H K : ∀ i, AddSubgroup (M i)) (φ : ∀ i, G →+ M i) (S : Finset ι)
    (hA : ∀ i, ∀ x ∈ A, φ i x ∈ K i) (hB : ∀ i, ∀ x ∈ B, φ i x ∈ H i)
    (hs : ∀ y : ∀ i, M i, (∀ i, y i ∈ K i) → ∃ x ∈ A, ∀ i ∈ S, φ i x - y i ∈ H i) :
    ∏ i ∈ S, (H i).relIndex (K i) ∣ B.relIndex A := by
  classical
  let ψ : A →+ (∀ i : S, K i ⧸ (H i).addSubgroupOf (K i)) :=
    AddMonoidHom.pi fun i : S => (QuotientAddGroup.mk' ((H i).addSubgroupOf (K i))).comp
      (((φ i).comp A.subtype).codRestrict (K i) fun x => hA i x x.2)
  have hψ : Function.Surjective ψ := by
    intro q
    choose r hr using fun i : S => QuotientAddGroup.mk_surjective (q i)
    obtain ⟨x, hx, h⟩ := hs (fun i => if hi : i ∈ S then (r ⟨i, hi⟩ : M i) else 0) (fun i => by
      by_cases hi : i ∈ S
      · simp only [hi, dif_pos]; exact (r ⟨i, hi⟩).2
      · simp only [hi, dif_neg, not_false_eq_true]; exact zero_mem _)
    refine ⟨⟨x, hx⟩, funext fun i => ?_⟩
    rw [← hr i]
    have h1 := h i i.2
    simp only [i.2, dif_pos] at h1
    show (QuotientAddGroup.mk (⟨φ i x, hA i x hx⟩ : K i) : K i ⧸ (H i).addSubgroupOf (K i)) = _
    rw [QuotientAddGroup.eq_iff_sub_mem, AddSubgroup.mem_addSubgroupOf]
    exact h1
  have hker : B.addSubgroupOf A ≤ ψ.ker := by
    intro x hx
    rw [AddMonoidHom.mem_ker]
    funext i
    show (QuotientAddGroup.mk (⟨φ i x, hA i x x.2⟩ : K i) : K i ⧸ (H i).addSubgroupOf (K i)) = 0
    rw [QuotientAddGroup.eq_zero_iff, AddSubgroup.mem_addSubgroupOf]
    exact hB i x hx
  have h1 : ψ.ker.index ∣ B.relIndex A := AddSubgroup.index_dvd_of_le hker
  rw [AddSubgroup.index_ker, AddMonoidHom.range_eq_top.2 hψ, AddSubgroup.card_top, Nat.card_pi] at h1
  rw [← Finset.prod_coe_sort S]
  exact h1

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}

theorem nsmul_mem_loc (v : HeightOneSpectrum (𝓞 F)) (T : ℕ) (L D : Submodule (𝓞 E) (Fin n → E))
    (h : ∀ y ∈ D, T • y ∈ L) : ∀ z ∈ loc v D, T • z ∈ loc v L := by
  intro z hz
  induction hz using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨y, hy, rfl⟩ := hx
    refine Submodule.subset_span ⟨T • y, h y hy, ?_⟩
    funext i
    simp only [Pi.smul_apply, map_nsmul]
  | zero => rw [smul_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [smul_add]; exact add_mem hx hy
  | smul a x _ hx => rw [smul_comm]; exact Submodule.smul_mem _ _ hx

theorem prod_loc_relIndex_dvd : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] (cm : CMData F E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHerm (cm.sig : E →+* E) J → J.det ≠ 0 → ∀ (T f : ℕ) (L : Submodule (𝓞 E) (Fin n → E)), T.Prime → SplitsIn E T → Module.finrank ℚ E = 2 * f → TLat cm.sig J T f L → ∀ (S : Finset (HeightOneSpectrum (𝓞 F))), (∀ v ∈ S, (T : 𝓞 F) ∈ v.asIdeal) → ∏ v ∈ S, (loc v L).toAddSubgroup.relIndex (loc v (dualL cm.sig J L)).toAddSubgroup ∣ L.toAddSubgroup.relIndex (dualL cm.sig J L).toAddSubgroup := by
  intro F E _ _ _ _ _ _ cm n J hJ hdet T f L hT _ _ hL S _
  obtain ⟨hlat, -, hTL, -, -⟩ := hL
  have hfin := (GlobalTheory.St.G.dualL_local_adelic F E cm n J hJ hdet L hlat).1.1
  have hTD : ∀ y ∈ dualL cm.sig J L, T • y ∈ L := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem x hx => rw [← Nat.cast_smul_eq_nsmul E]; exact hTL x hx
    | zero => rw [smul_zero]; exact zero_mem _
    | add x y _ _ hx hy => rw [smul_add]; exact add_mem hx hy
    | smul a x _ hx => rw [smul_comm]; exact Submodule.smul_mem _ _ hx
  refine prod_relIndex_dvd (M := fun v : HeightOneSpectrum (𝓞 F) => Fin n → E ⊗[F] v.adicCompletion F)
    L.toAddSubgroup (dualL cm.sig J L).toAddSubgroup (fun v => (loc v L).toAddSubgroup)
    (fun v => (loc v (dualL cm.sig J L)).toAddSubgroup)
    (fun v => AddMonoidHom.compLeft (inclE (F := F) (E := E) (v.adicCompletion F)).toAddMonoidHom (Fin n)) S
    (fun v x hx => Submodule.subset_span ⟨x, hx, rfl⟩) (fun v x hx => Submodule.subset_span ⟨x, hx, rfl⟩) ?_
  intro y hy
  obtain ⟨x, hx, h⟩ := GlobalTheory.OverCompare.exists_lattice_approx_all F E n (dualL cm.sig J L) hfin T hT.ne_zero y hy
  refine ⟨x, hx, fun v _ => ?_⟩
  obtain ⟨z, hz, e⟩ := h v
  have h1 := nsmul_mem_loc v T L _ hTD z hz
  have e2 : (fun i => inclE (F := F) (v.adicCompletion F) (x i)) - y v = -(T • z) := by
    rw [e]; abel
  show (fun i => inclE (F := F) (v.adicCompletion F) (x i)) - y v ∈ loc v L
  rw [e2]
  exact neg_mem h1

end GlobalTheory.St.G.GlobIdx

import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.PProjA
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsUnipLevIntegral
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.GenericFiniteByInduction

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Formalism.L2.Host
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec GlobalTheory.CompanionTheory.CTFin

namespace PositivityTheory.Rg.Rs.InductionInStages

variable {R : Type} [CommRing R] {a d₁ d₂ r s : ℕ}

theorem val_stdBlocks_const {d N : ℕ} (h : ∑ _ : Fin d, a = N) (b : Fin d) (i : Fin a) :
    ((stdBlocks (fun _ : Fin d => a) h ⟨b, i⟩ : Fin N) : ℕ) = (b : ℕ) * a + i := by
  rw [stdBlocks_val]
  simp

theorem sum_const_eq {d N : ℕ} (h : ∑ _ : Fin d, a = N) : N = d * a := by
  rw [← h]
  simp

theorem stdBlocks_castAdd (h₁ : ∑ _ : Fin d₁, a = r) (H : ∑ _ : Fin (d₁ + d₂), a = r + s) (b : Fin d₁) (i : Fin a) :
    stdBlocks (fun _ : Fin (d₁ + d₂) => a) H ⟨Fin.castAdd d₂ b, i⟩ = Fin.castAdd s (stdBlocks (fun _ : Fin d₁ => a) h₁ ⟨b, i⟩) := by
  apply Fin.ext
  rw [val_stdBlocks_const, Fin.coe_castAdd, Fin.coe_castAdd, val_stdBlocks_const]

theorem stdBlocks_natAdd (h₁ : ∑ _ : Fin d₁, a = r) (h₂ : ∑ _ : Fin d₂, a = s) (H : ∑ _ : Fin (d₁ + d₂), a = r + s)
    (b : Fin d₂) (i : Fin a) :
    stdBlocks (fun _ : Fin (d₁ + d₂) => a) H ⟨Fin.natAdd d₁ b, i⟩ = Fin.natAdd r (stdBlocks (fun _ : Fin d₂ => a) h₂ ⟨b, i⟩) := by
  apply Fin.ext
  simp only [val_stdBlocks_const, Fin.val_natAdd, sum_const_eq h₁]
  ring

theorem lev_cc (m : GL (Fin r) R × GL (Fin s) R) (i j : Fin r) :
    (lev R r s m : Matrix (Fin (r + s)) (Fin (r + s)) R) (Fin.castAdd s i) (Fin.castAdd s j) = (m.1 : Matrix _ _ R) i j := by
  simp [GlobalTheory.SmGL.val_emb₂, GlobalTheory.SmGL.stdSum]

theorem lev_nn (m : GL (Fin r) R × GL (Fin s) R) (i j : Fin s) :
    (lev R r s m : Matrix (Fin (r + s)) (Fin (r + s)) R) (Fin.natAdd r i) (Fin.natAdd r j) = (m.2 : Matrix _ _ R) i j := by
  simp [GlobalTheory.SmGL.val_emb₂, GlobalTheory.SmGL.stdSum]

theorem lev_cn (m : GL (Fin r) R × GL (Fin s) R) (i : Fin r) (j : Fin s) :
    (lev R r s m : Matrix (Fin (r + s)) (Fin (r + s)) R) (Fin.castAdd s i) (Fin.natAdd r j) = 0 := by
  simp [GlobalTheory.SmGL.val_emb₂, GlobalTheory.SmGL.stdSum]

theorem lev_nc (m : GL (Fin r) R × GL (Fin s) R) (i : Fin s) (j : Fin r) :
    (lev R r s m : Matrix (Fin (r + s)) (Fin (r + s)) R) (Fin.natAdd r i) (Fin.castAdd s j) = 0 := by
  simp [GlobalTheory.SmGL.val_emb₂, GlobalTheory.SmGL.stdSum]

theorem unip_col (x : BlockIx (r + s) r → R) (i : Fin (r + s)) (k : Fin r) :
    ((unip x : GL (Fin (r + s)) R) : Matrix _ _ R) i (Fin.castAdd s k) =
      (1 : Matrix (Fin (r + s)) (Fin (r + s)) R) i (Fin.castAdd s k) := by
  change ((1 : Matrix (Fin (r + s)) (Fin (r + s)) R) + nilM x) i (Fin.castAdd s k) = _
  rw [Matrix.add_apply]
  have h0 : nilM x i (Fin.castAdd s k) = 0 := by
    simp only [nilM, Matrix.of_apply, Fin.coe_castAdd]
    rw [dif_neg]
    intro h
    exact absurd h.2 (not_le.2 k.isLt)
  rw [h0, add_zero]

theorem unip_row (x : BlockIx (r + s) r → R) (k : Fin s) (j : Fin (r + s)) :
    ((unip x : GL (Fin (r + s)) R) : Matrix _ _ R) (Fin.natAdd r k) j =
      (1 : Matrix (Fin (r + s)) (Fin (r + s)) R) (Fin.natAdd r k) j := by
  change ((1 : Matrix (Fin (r + s)) (Fin (r + s)) R) + nilM x) (Fin.natAdd r k) j = _
  rw [Matrix.add_apply]
  have h0 : nilM x (Fin.natAdd r k) j = 0 := by
    simp only [nilM, Matrix.of_apply, Fin.coe_natAdd]
    rw [dif_neg]
    intro h
    omega
  rw [h0, add_zero]

theorem unip_lev_cc (x : BlockIx (r + s) r → R) (m : GL (Fin r) R × GL (Fin s) R) (i j : Fin r) :
    ((unip x * lev R r s m : GL (Fin (r + s)) R) : Matrix _ _ R) (Fin.castAdd s i) (Fin.castAdd s j) = (m.1 : Matrix _ _ R) i j := by
  simp only [Units.val_mul, Matrix.mul_apply, Fin.sum_univ_add, unip_col, lev_nc, lev_cc, mul_zero,
    Finset.sum_const_zero, add_zero, Matrix.one_apply, Fin.castAdd_inj, ite_mul, one_mul, zero_mul,
    Finset.sum_ite_eq, Finset.mem_univ, if_true]

theorem unip_lev_nn (x : BlockIx (r + s) r → R) (m : GL (Fin r) R × GL (Fin s) R) (i j : Fin s) :
    ((unip x * lev R r s m : GL (Fin (r + s)) R) : Matrix _ _ R) (Fin.natAdd r i) (Fin.natAdd r j) = (m.2 : Matrix _ _ R) i j := by
  simp only [Units.val_mul, Matrix.mul_apply, unip_row]
  rw [← Matrix.mul_apply, Matrix.one_mul, lev_nn]

theorem castAdd_or_natAdd (b : Fin (d₁ + d₂)) : (∃ c, b = Fin.castAdd d₂ c) ∨ ∃ c, b = Fin.natAdd d₁ c := by
  rcases lt_or_ge (b : ℕ) d₁ with h | h
  · exact Or.inl ⟨⟨b, h⟩, Fin.ext rfl⟩
  · refine Or.inr ⟨⟨b - d₁, by omega⟩, Fin.ext ?_⟩
    simp only [Fin.coe_natAdd]
    omega

theorem leviEmb_split (h₁ : ∑ _ : Fin d₁, a = r) (h₂ : ∑ _ : Fin d₂, a = s) (H : ∑ _ : Fin (d₁ + d₂), a = r + s)
    (m : ∀ _ : Fin (d₁ + d₂), GL (Fin a) R) :
    leviEmb R (stdBlocks (fun _ : Fin (d₁ + d₂) => a) H) m =
      lev R r s (leviEmb R (stdBlocks (fun _ : Fin d₁ => a) h₁) (fun b => m (Fin.castAdd d₂ b)),
        leviEmb R (stdBlocks (fun _ : Fin d₂ => a) h₂) (fun b => m (Fin.natAdd d₁ b))) := by
  have hcn : ∀ (c : Fin d₁) (c' : Fin d₂), Fin.castAdd d₂ c ≠ Fin.natAdd d₁ c' := by
    intro c c' h
    have h1 := congrArg Fin.val h
    have h2 := c.isLt
    simp only [Fin.coe_castAdd, Fin.coe_natAdd] at h1
    omega
  apply Units.ext
  ext p q
  obtain ⟨⟨b, i⟩, rfl⟩ := (stdBlocks (fun _ : Fin (d₁ + d₂) => a) H).surjective p
  obtain ⟨⟨b', j⟩, rfl⟩ := (stdBlocks (fun _ : Fin (d₁ + d₂) => a) H).surjective q
  rcases castAdd_or_natAdd b with ⟨c, rfl⟩ | ⟨c, rfl⟩ <;>
    rcases castAdd_or_natAdd b' with ⟨c', rfl⟩ | ⟨c', rfl⟩
  · by_cases hc : c = c'
    · subst hc
      rw [leviEmb_apply_same, stdBlocks_castAdd h₁ H, stdBlocks_castAdd h₁ H, lev_cc, leviEmb_apply_same]
    · rw [leviEmb_apply_ne R _ _ (fun h => hc (Fin.castAdd_injective _ _ h)), stdBlocks_castAdd h₁ H,
        stdBlocks_castAdd h₁ H, lev_cc, leviEmb_apply_ne R _ _ hc]
  · rw [leviEmb_apply_ne R _ _ (hcn c c'), stdBlocks_castAdd h₁ H, stdBlocks_natAdd h₁ h₂ H, lev_cn]
  · rw [leviEmb_apply_ne R _ _ (fun h => hcn c' c h.symm), stdBlocks_natAdd h₁ h₂ H,
      stdBlocks_castAdd h₁ H, lev_nc]
  · by_cases hc : c = c'
    · subst hc
      rw [leviEmb_apply_same, stdBlocks_natAdd h₁ h₂ H, stdBlocks_natAdd h₁ h₂ H, lev_nn, leviEmb_apply_same]
    · rw [leviEmb_apply_ne R _ _ (fun h => hc (Fin.natAdd_injective _ _ h)), stdBlocks_natAdd h₁ h₂ H,
        stdBlocks_natAdd h₁ h₂ H, lev_nn, leviEmb_apply_ne R _ _ hc]

theorem unipRad_split (h₁ : ∑ _ : Fin d₁, a = r) (h₂ : ∑ _ : Fin d₂, a = s) (H : ∑ _ : Fin (d₁ + d₂), a = r + s)
    {v : GL (Fin (r + s)) R} (hv : v ∈ unipRad R (stdBlocks (fun _ : Fin (d₁ + d₂) => a) H)) :
    ∃ (x : BlockIx (r + s) r → R) (v₁ : GL (Fin r) R) (v₂ : GL (Fin s) R),
      v₁ ∈ unipRad R (stdBlocks (fun _ : Fin d₁ => a) h₁) ∧ v₂ ∈ unipRad R (stdBlocks (fun _ : Fin d₂ => a) h₂) ∧
      v = unip x * lev R r s (v₁, v₂) := by
  have low : ∀ g : GL (Fin (r + s)) R, g ∈ parab R (stdBlocks (fun _ : Fin (d₁ + d₂) => a) H) →
      ∀ i j : Fin (r + s), r ≤ (i : ℕ) → (j : ℕ) < r → (g : Matrix _ _ R) i j = 0 := by
    intro g hg i j hi hj
    rw [mem_parab_iff] at hg
    have hi' := i.isLt
    obtain ⟨i', rfl⟩ : ∃ i' : Fin s, i = Fin.natAdd r i' :=
      ⟨⟨i - r, by omega⟩, Fin.ext (by simp only [Fin.coe_natAdd]; omega)⟩
    obtain ⟨j', rfl⟩ : ∃ j' : Fin r, j = Fin.castAdd s j' := ⟨⟨j, hj⟩, rfl⟩
    obtain ⟨⟨c, i''⟩, rfl⟩ := (stdBlocks (fun _ : Fin d₂ => a) h₂).surjective i'
    obtain ⟨⟨c', j''⟩, rfl⟩ := (stdBlocks (fun _ : Fin d₁ => a) h₁).surjective j'
    rw [← stdBlocks_natAdd h₁ h₂ H, ← stdBlocks_castAdd h₁ H]
    apply hg
    have := c'.isLt
    rw [Fin.lt_def]
    simp only [Fin.coe_castAdd, Fin.coe_natAdd]
    omega
  obtain ⟨hvP, hvD⟩ := mem_unipRad.1 hv
  have hvP' := mem_parab_iff.1 hvP
  have hinvP : v⁻¹ ∈ parab R (stdBlocks (fun _ : Fin (d₁ + d₂) => a) H) :=
    (mem_unipRad.1 ((unipRad R _).inv_mem hv)).1
  obtain ⟨x, m, hvm⟩ := GlobalTheory.CompanionTheory.CTFin.IwaFin.exists_unip_mul_lev r s v (low v hvP) (low v⁻¹ hinvP)
  refine ⟨x, m.1, m.2, ?_, ?_, hvm⟩
  · rw [mem_unipRad, mem_parab_iff]
    constructor
    · intro α β i j hβα
      rw [← unip_lev_cc x m, ← hvm, ← stdBlocks_castAdd h₁ H, ← stdBlocks_castAdd h₁ H]
      apply hvP'
      rw [Fin.lt_def] at hβα ⊢
      simpa only [Fin.coe_castAdd] using hβα
    · intro α i j
      rw [← unip_lev_cc x m, ← hvm, ← stdBlocks_castAdd h₁ H, ← stdBlocks_castAdd h₁ H]
      exact hvD _ _ _
  · rw [mem_unipRad, mem_parab_iff]
    constructor
    · intro α β i j hβα
      rw [← unip_lev_nn x m, ← hvm, ← stdBlocks_natAdd h₁ h₂ H, ← stdBlocks_natAdd h₁ h₂ H]
      apply hvP'
      rw [Fin.lt_def] at hβα ⊢
      simp only [Fin.coe_natAdd]
      omega
    · intro α i j
      rw [← unip_lev_nn x m, ← hvm, ← stdBlocks_natAdd h₁ h₂ H, ← stdBlocks_natAdd h₁ h₂ H]
      exact hvD _ _ _

end PositivityTheory.Rg.Rs.InductionInStages

end

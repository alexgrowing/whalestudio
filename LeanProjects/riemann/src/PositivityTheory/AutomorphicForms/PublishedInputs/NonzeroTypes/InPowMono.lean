import PositivityTheory.AutomorphicForms.PublishedInputs.NonzeroTypes.NonzeroLeviEigenvectorExists
import Development.AbelianVarietyTheory.Definitions.Divisors.T2SpaceGeneralLinearGroup

noncomputable section

open scoped Classical

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL ValuativeRel Matrix

namespace UpperTheory.TNZ.Grp

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

namespace P_PJ

variable {n : ℕ} (G : Grp k n)

theorem inPow_mono {a b : ℕ} (hab : a ≤ b) {x : k} (hx : InPow b x) : InPow a x := by
  obtain ⟨y, hy, rfl⟩ := hx
  exact ⟨y, Ideal.pow_le_pow_right hab hy, rfl⟩

theorem KC_mono {a b : ℕ} (hab : a ≤ b) : KC k n b ⊆ KC k n a := fun _ hg =>
  ⟨hg.1, fun i j => inPow_mono hab (hg.2 i j)⟩

def Jsub (h1 : (1 : GL (Fin n) k) ∈ G.JSet) (hmul : ∀ g ∈ G.JSet, ∀ h ∈ G.JSet, g * h ∈ G.JSet)
    (hinv : ∀ g ∈ G.JSet, g⁻¹ ∈ G.JSet) : Subgroup (GL (Fin n) k) where
  carrier := G.JSet
  one_mem' := h1
  mul_mem' := fun ha hb => hmul _ ha _ hb
  inv_mem' := fun ha => hinv _ ha

theorem Jg_sub (h1 : (1 : GL (Fin n) k) ∈ G.JSet) (hmul : ∀ g ∈ G.JSet, ∀ h ∈ G.JSet, g * h ∈ G.JSet)
    (hinv : ∀ g ∈ G.JSet, g⁻¹ ∈ G.JSet) {g : GL (Fin n) k} (hg : g ∈ G.Jg) : g ∈ G.JSet :=
  (Subgroup.closure_le (K := Jsub G h1 hmul hinv)).2 (fun _ hx => hx) hg

theorem Jg_le_KO (h1 : (1 : GL (Fin n) k) ∈ G.JSet) (hmul : ∀ g ∈ G.JSet, ∀ h ∈ G.JSet, g * h ∈ G.JSet)
    (hinv : ∀ g ∈ G.JSet, g⁻¹ ∈ G.JSet) : G.Jg ≤ KO k (Fin n) := fun _ hg =>
  (Jg_sub G h1 hmul hinv hg).1

theorem core (h1 : (1 : GL (Fin n) k) ∈ G.JSet) (hmul : ∀ g ∈ G.JSet, ∀ h ∈ G.JSet, g * h ∈ G.JSet)
    (hinv : ∀ g ∈ G.JSet, g⁻¹ ∈ G.JSet)
    (hlM : ∀ g ∈ G.JSet, ∀ h ∈ G.JSet, G.lam (g * h) = G.lam g * G.lam h)
    (hlB : G.lam 1 = 1 ∧ (∀ g, G.lam g ≠ 0) ∧ ∀ g ∈ KC k n G.lev, G.lam g = 1)
    (hKC : ∀ r : ℕ, ((KCg k n r : Set (GL (Fin n) k)) = KC k n r) ∧
      (∀ g ∈ KO k (Fin n), ∀ u ∈ KC k n r, g * u * g⁻¹ ∈ KC k n r) ∧ IsOpen (KC k n r) ∧
        KC k n r ⊆ (KO k (Fin n) : Set _) ∧ (G.lev ≤ r → KC k n r ⊆ G.JSet))
    (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin n) k) V) (r : ℕ) (hr : G.lev ≤ r) :
    Finite (↥G.Jg ⧸ (KCg k n r).subgroupOf G.Jg) ∧
    ∀ v : V, (∀ u ∈ KC k n r, π u v = v) →
      G.PJ π r v ∈ G.Eig π ∧ (∀ j ∈ G.JSet, G.PJ π r (π j v) = G.lam j • G.PJ π r v) ∧
      (v ∈ G.Eig π → G.PJ π r v = (Nat.card (↥G.Jg ⧸ (KCg k n r).subgroupOf G.Jg) : ℂ) • v) := by
  obtain ⟨hKCeq, hKCn, hKCo, -, -⟩ := hKC r
  have hJ : ∀ {g : GL (Fin n) k}, g ∈ G.Jg → g ∈ G.JSet := fun hg => Jg_sub G h1 hmul hinv hg
  have hJK := Jg_le_KO G h1 hmul hinv
  have hKCmem : ∀ {u : GL (Fin n) k}, u ∈ KCg k n r → u ∈ KC k n r := fun hu => by
    rw [← hKCeq]; exact hu

  have hfin : Finite (↥G.Jg ⧸ (KCg k n r).subgroupOf G.Jg) := by
    have hc : IsCompact (KO k (Fin n) : Set (GL (Fin n) k)) := GlobalTheory.SplitFlip.isCompact_KO
    have : CompactSpace (KO k (Fin n)) := isCompact_iff_compactSpace.1 hc
    have ho : IsOpen (((KCg k n r).subgroupOf (KO k (Fin n)) : Subgroup (KO k (Fin n))) : Set (KO k (Fin n))) := by
      have : IsOpen (KCg k n r : Set (GL (Fin n) k)) := by rw [hKCeq]; exact hKCo
      exact this.preimage continuous_subtype_val
    have : Finite (KO k (Fin n) ⧸ (KCg k n r).subgroupOf (KO k (Fin n))) := Subgroup.quotient_finite_of_isOpen _ ho
    have h0 : (KCg k n r).relIndex (KO k (Fin n)) ≠ 0 := Subgroup.index_ne_zero_of_finite
    have h0' : (KCg k n r).relIndex G.Jg ≠ 0 := fun h => h0 (Subgroup.relIndex_eq_zero_of_le_right hJK h)
    have : ((KCg k n r).subgroupOf G.Jg).FiniteIndex := ⟨h0'⟩
    exact Subgroup.finite_quotient_of_finiteIndex
  refine ⟨hfin, fun v hv => ?_⟩
  let _ : Fintype (↥G.Jg ⧸ (KCg k n r).subgroupOf G.Jg) := Fintype.ofFinite _
  have hN : ((KCg k n r).subgroupOf G.Jg).Normal := ⟨fun h hh g => by
    rw [Subgroup.mem_subgroupOf] at hh ⊢
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    exact Subgroup.subset_closure (hKCn _ (hJK g.2) _ (hKCmem hh))⟩
  obtain ⟨f, hfdef⟩ : ∃ f : ↥G.Jg → V, ∀ x, f x = (G.lam x)⁻¹ • π x v := ⟨_, fun _ => rfl⟩
  have hlamH : ∀ h : ↥G.Jg, h ∈ (KCg k n r).subgroupOf G.Jg → G.lam h = 1 := fun h hh =>
    hlB.2.2 _ (KC_mono hr (hKCmem (Subgroup.mem_subgroupOf.1 hh)))
  have hπH : ∀ h : ↥G.Jg, h ∈ (KCg k n r).subgroupOf G.Jg → π h v = v := fun h hh =>
    hv _ (hKCmem (Subgroup.mem_subgroupOf.1 hh))
  have hf : ∀ x y : ↥G.Jg, (x : ↥G.Jg ⧸ (KCg k n r).subgroupOf G.Jg) = y → f x = f y := by
    intro x y hxy
    obtain ⟨h, hh, rfl⟩ : ∃ h ∈ (KCg k n r).subgroupOf G.Jg, y = x * h :=
      ⟨x⁻¹ * y, QuotientGroup.eq.1 hxy, by group⟩
    rw [hfdef, hfdef, Subgroup.coe_mul, hlM _ (hJ x.2) _ (hJ h.2), hlamH h hh, mul_one, map_mul,
      Module.End.mul_apply, hπH h hh]
  have hPJ : ∀ w : V, G.PJ π r w = ∑ c : ↥G.Jg ⧸ (KCg k n r).subgroupOf G.Jg,
      (G.lam ((Quotient.out c : ↥G.Jg) : GL (Fin n) k))⁻¹ • π ((Quotient.out c : ↥G.Jg) : GL (Fin n) k) w :=
    fun w => finsum_eq_sum_of_fintype _
  have hPJv : G.PJ π r v = ∑ c : ↥G.Jg ⧸ (KCg k n r).subgroupOf G.Jg, f (Quotient.out c) := by
    rw [hPJ]; simp only [hfdef]
  have hA : ∀ g ∈ G.JSet, π g (G.PJ π r v) = G.lam g • G.PJ π r v := by
    intro g hg
    have hg0 := hlB.2.1 g
    have hterm : ∀ x : ↥G.Jg, π g (f x) = G.lam g • f (⟨g, Subgroup.subset_closure hg⟩ * x) := by
      intro x
      rw [hfdef, hfdef, Subgroup.coe_mul, Subgroup.coe_mk, hlM g hg _ (hJ x.2), map_smul, map_mul,
        Module.End.mul_apply, smul_smul]
      congr 1
      field_simp
    have hmv : ∀ c : ↥G.Jg ⧸ (KCg k n r).subgroupOf G.Jg,
        f (⟨g, Subgroup.subset_closure hg⟩ * Quotient.out c) =
          f (Quotient.out ((QuotientGroup.mk ⟨g, Subgroup.subset_closure hg⟩ : ↥G.Jg ⧸ (KCg k n r).subgroupOf G.Jg) * c)) := by
      intro c
      apply hf
      rw [QuotientGroup.out_eq', QuotientGroup.mk_mul, QuotientGroup.out_eq']
    rw [hPJv, map_sum, Finset.smul_sum]
    simp_rw [hterm, hmv]
    exact Fintype.sum_equiv (Equiv.mulLeft (QuotientGroup.mk ⟨g, Subgroup.subset_closure hg⟩ :
      ↥G.Jg ⧸ (KCg k n r).subgroupOf G.Jg)) _ _ (fun c => rfl)
  refine ⟨fun g hg => hA g hg, fun j hj => ?_, fun hEv => ?_⟩
  · have hjinv := hinv j hj
    have h1' : G.lam j⁻¹ * G.lam j = 1 := by rw [← hlM _ hjinv _ hj, inv_mul_cancel, hlB.1]
    have hterm : ∀ x : ↥G.Jg, (G.lam x)⁻¹ • π x (π j v) =
        π j (f ((⟨j, Subgroup.subset_closure hj⟩ : ↥G.Jg)⁻¹ * x * ⟨j, Subgroup.subset_closure hj⟩)) := by
      intro x
      have hx := hJ x.2
      have e : (((⟨j, Subgroup.subset_closure hj⟩ : ↥G.Jg)⁻¹ * x * ⟨j, Subgroup.subset_closure hj⟩ : ↥G.Jg) :
          GL (Fin n) k) = j⁻¹ * x * j := rfl
      have hl : G.lam (((⟨j, Subgroup.subset_closure hj⟩ : ↥G.Jg)⁻¹ * x * ⟨j, Subgroup.subset_closure hj⟩ : ↥G.Jg) :
          GL (Fin n) k) = G.lam x := by
        rw [e, hlM _ (hmul _ hjinv _ hx) _ hj, hlM _ hjinv _ hx]
        linear_combination G.lam x * h1'
      rw [hfdef, hl, map_smul, e, ← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul]
      congr 3
      group
    have hmv : ∀ c : ↥G.Jg ⧸ (KCg k n r).subgroupOf G.Jg,
        f ((⟨j, Subgroup.subset_closure hj⟩ : ↥G.Jg)⁻¹ * Quotient.out c * ⟨j, Subgroup.subset_closure hj⟩) =
          f (Quotient.out ((QuotientGroup.mk ⟨j, Subgroup.subset_closure hj⟩ : ↥G.Jg ⧸ (KCg k n r).subgroupOf G.Jg)⁻¹ * c *
            QuotientGroup.mk ⟨j, Subgroup.subset_closure hj⟩)) := by
      intro c
      apply hf
      rw [QuotientGroup.out_eq', QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv, QuotientGroup.out_eq']
    rw [hPJ (π j v)]
    simp_rw [hterm, hmv]
    rw [← map_sum, ← hA j hj, hPJv]
    congr 1
    exact Fintype.sum_equiv ((Equiv.mulLeft (QuotientGroup.mk ⟨j, Subgroup.subset_closure hj⟩ :
      ↥G.Jg ⧸ (KCg k n r).subgroupOf G.Jg)⁻¹).trans (Equiv.mulRight (QuotientGroup.mk ⟨j, Subgroup.subset_closure hj⟩ :
      ↥G.Jg ⧸ (KCg k n r).subgroupOf G.Jg))) _ _ (fun c => rfl)
  · have hfv : ∀ x : ↥G.Jg, f x = v := fun x => by
      rw [hfdef, hEv _ (hJ x.2), smul_smul, inv_mul_cancel₀ (hlB.2.1 _), one_smul]
    rw [hPJv]
    simp_rw [hfv]
    rw [Finset.sum_const, Finset.card_univ, Nat.card_eq_fintype_card, Nat.cast_smul_eq_nsmul]

end P_PJ

theorem step_PJ {n : ℕ} (G : Grp k n) : ParabolicJacquetProp G := by
  intro hcb hccB hΔU hΔM hJone hJmul hJinv hlM hlB hKC
  exact P_PJ.core G hJone.1 (hJmul hcb hccB) (hJinv hcb hccB) (hlM hcb hΔU hΔM hccB) (hlB hccB) (hKC hccB)

end UpperTheory.TNZ.Grp

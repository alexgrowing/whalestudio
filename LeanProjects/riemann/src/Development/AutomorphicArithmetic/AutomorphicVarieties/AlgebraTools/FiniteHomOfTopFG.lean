import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.ProfDefs

open Filter UpperTheory.V.AlgebraTools
open scoped TensorProduct

private theorem fgHom_mem_of_closed {G : Type} [Group G] [TopologicalSpace G] {s : Set G}
    (hs : TopGen s) (E : Subgroup G) (hE : IsClosed (E : Set G)) (hsE : s ⊆ E) (g : G) : g ∈ E := by
  have h1 : (Subgroup.closure s : Set G) ⊆ E := (Subgroup.closure_le E).2 hsE
  have h2 : closure (Subgroup.closure s : Set G) ⊆ E := closure_minimal h1 hE
  exact h2 (hs g)

private theorem fgHom_part1 {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (hG : TopFG G) (Z : Type) [Group Z] [Finite Z] :
    {f : G →* Z | IsOpen (f.ker : Set G)}.Finite := by
  obtain ⟨s, hsf, hs⟩ := hG
  haveI : Finite s := hsf.to_subtype
  refine Set.Finite.of_finite_image (f := fun f : G →* Z => fun x : s => f x) (Set.toFinite _) ?_
  intro f hf f' hf' h
  have hle : f.ker ⊓ f'.ker ≤ f.eqLocus f' := by
    intro x hx
    have h1 : f x = 1 := hx.1
    have h2 : f' x = 1 := hx.2
    show f x = f' x
    rw [h1, h2]
  have hop : IsOpen ((f.ker ⊓ f'.ker : Subgroup G) : Set G) := IsOpen.inter hf hf'
  have hcl : IsClosed (f.eqLocus f' : Set G) :=
    Subgroup.isClosed_of_isOpen _ (Subgroup.isOpen_mono hle hop)
  ext g
  exact fgHom_mem_of_closed hs _ hcl (fun x hx => congrFun h ⟨x, hx⟩) g

private theorem fgHom_part2 {G : Type} [Group G] [TopologicalSpace G]
    (hG : TopFG G) (M : Type) [AddCommGroup M] [Finite M] [DistribMulAction G M] :
    {c : G → M | IsLocallyConstant c ∧ ∀ g h, c (g * h) = c g + g • c h}.Finite := by
  obtain ⟨s, hsf, hs⟩ := hG
  haveI : Finite s := hsf.to_subtype
  refine Set.Finite.of_finite_image (f := fun c : G → M => fun x : s => c x) (Set.toFinite _) ?_
  intro c hc c' hc' h
  have one : ∀ d : G → M, (∀ g h, d (g * h) = d g + g • d h) → d 1 = 0 := by
    intro d hd
    have := hd 1 1
    rw [one_mul, one_smul] at this
    exact left_eq_add.1 this
  let E : Subgroup G :=
    { carrier := {g | c g = c' g}
      mul_mem' := by
        intro a b ha hb
        have ha' : c a = c' a := ha
        have hb' : c b = c' b := hb
        show c (a * b) = c' (a * b)
        rw [hc.2, hc'.2, ha', hb']
      one_mem' := by
        show c 1 = c' 1
        rw [one c hc.2, one c' hc'.2]
      inv_mem' := by
        intro a ha
        have ha' : c a = c' a := ha
        show c a⁻¹ = c' a⁻¹
        have h1 := hc.2 a a⁻¹
        have h2 := hc'.2 a a⁻¹
        rw [mul_inv_cancel, one c hc.2] at h1
        rw [mul_inv_cancel, one c' hc'.2, ← ha'] at h2
        exact MulAction.injective a (add_left_cancel (h1.symm.trans h2)) }
  have hcl : IsClosed (E : Set G) := by
    have := (hc.1.prodMk hc'.1) {p : M × M | p.1 ≠ p.2}
    rw [← isOpen_compl_iff]
    exact this
  funext g
  exact fgHom_mem_of_closed hs E hcl (fun x hx => congrFun h ⟨x, hx⟩) g

private theorem fgHom_part3 {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (hG : TopFG G) (n : ℕ) (hn : n ≠ 0) :
    {H : Subgroup G | IsOpen (H : Set G) ∧ H.index = n}.Finite := by
  have h1 := (fgHom_part1 hG (Equiv.Perm (Fin n))).prod (Set.finite_univ (α := Fin n))
  refine (h1.image fun p => (MulAction.stabilizer (Equiv.Perm (Fin n)) p.2).comap p.1).subset ?_
  rintro H ⟨hH, hi⟩
  haveI : H.FiniteIndex := ⟨hi ▸ hn⟩
  have e : (G ⧸ H) ≃ Fin n := Finite.equivFinOfCardEq hi
  refine ⟨(e.permCongrHom.toMonoidHom.comp (MulAction.toPermHom G (G ⧸ H)), e ((1 : G) : G ⧸ H)),
    ⟨?_, trivial⟩, ?_⟩
  · have hop : IsOpen (H.normalCore : Set G) :=
      Subgroup.isOpen_of_isClosed_of_finiteIndex _
        (Subgroup.normalCore_isClosed H (Subgroup.isClosed_of_isOpen H hH))
    refine Subgroup.isOpen_mono ?_ hop
    intro g hg
    rw [Subgroup.normalCore_eq_ker, MonoidHom.mem_ker] at hg
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, hg, map_one]
  · ext g
    simp only [Subgroup.mem_comap, MulAction.mem_stabilizer_iff]
    have : (e.permCongrHom.toMonoidHom.comp (MulAction.toPermHom G (G ⧸ H))) g • e ((1 : G) : G ⧸ H)
        = e ((g : G) : G ⧸ H) := by
      simp [Equiv.Perm.smul_def]
    rw [this, e.injective.eq_iff, eq_comm, QuotientGroup.eq, inv_one, one_mul]

theorem UpperTheory.V.AlgebraTools.finite_hom_of_topFG :
    ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G], TopFG G →
      (∀ (Z : Type) [Group Z] [Finite Z], {f : G →* Z | IsOpen (f.ker : Set G)}.Finite) ∧
      (∀ (M : Type) [AddCommGroup M] [Finite M] [DistribMulAction G M], (∀ m : M, IsLocallyConstant fun g : G => g • m) →
        {c : G → M | IsLocallyConstant c ∧ ∀ g h, c (g * h) = c g + g • c h}.Finite) ∧
      (∀ n : ℕ, n ≠ 0 → {H : Subgroup G | IsOpen (H : Set G) ∧ H.index = n}.Finite) := by
  intro G _ _ _ hG
  exact ⟨fun Z _ _ => fgHom_part1 hG Z, fun M _ _ _ _ => fgHom_part2 hG M,
    fun n hn => fgHom_part3 hG n hn⟩

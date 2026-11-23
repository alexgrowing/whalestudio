import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IwahoriTypeSupport.TorusScalar

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL ValuativeRel Matrix UpperTheory.Gal.TypesAndIwahori

private theorem typeToIw_key (hF : UpperTheory.Gal.TypesAndIwahori.FinTri) {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] {N s : ℕ} (d : Fin s → ℕ) (hd : ∑ a, d a = N) {g : GL (Fin N) k}
    (hg : g ∈ KO k (Fin N)) (hlow : ∀ i j, j < i → valuation k ((g : Matrix (Fin N) (Fin N) k) i j) < 1) :
    ∃ hpar : g ∈ parahoric k (stdBlocks d hd), ∀ a,
      ((GeneralLinearGroup.det (parahoricProj k (stdBlocks d hd) ⟨g, hpar⟩ a) : 𝓀[k]ˣ) : 𝓀[k]) =
        ∏ j : Fin (d a), (redK k (Fin N) ⟨g, hg⟩ : Matrix (Fin N) (Fin N) 𝓀[k])
          (stdBlocks d hd ⟨a, j⟩) (stdBlocks d hd ⟨a, j⟩) := by
  obtain ⟨hp, hdet⟩ := hF 𝓀[k] N s d hd (redK k (Fin N) ⟨g, hg⟩) (fun i j hij => by
    rw [redK_eq_zero_iff]
    exact hlow i j hij)
  refine ⟨mem_levelPre.2 ⟨hg, hp⟩, fun a => ?_⟩
  exact hdet a

theorem UpperTheory.Gal.TypesAndIwahori.typeToIw :
    UpperTheory.Gal.TypesAndIwahori.FinTri → UpperTheory.Gal.TypesAndIwahori.TypeToIw := by
  intro hF k _ _ _ _ N s d hd V _ _ π θ μ hμ v hv
  rw [mem_typeSp] at hv
  constructor
  · intro h hK hlow hdiag
    obtain ⟨hpar, hdet⟩ := typeToIw_key hF d hd hK hlow
    have hv' := hv ⟨h, hpar⟩
    have hone : ∀ a, GeneralLinearGroup.det (parahoricProj k (stdBlocks d hd) ⟨h, hpar⟩ a) = 1 := by
      intro a
      ext
      rw [hdet a, Units.val_one]
      apply Finset.prod_eq_one
      intro j _
      have hx := (redK_eq_iff (k := k) ⟨h, hK⟩ (stdBlocks d hd ⟨a, j⟩) (stdBlocks d hd ⟨a, j⟩) 1).2 (by
        simpa using hdiag (stdBlocks d hd ⟨a, j⟩))
      simpa using hx
    rw [typeChar_apply] at hv'
    simpa [hone] using hv'
  · intro t ht
    have hI := mem_iwahori.1 (diagT_mem_iwahori (k := k) ht)
    obtain ⟨hpar, hdet⟩ := typeToIw_key hF d hd hI.1 hI.2
    have hv' := hv ⟨_, hpar⟩
    rw [typeChar_apply] at hv'
    refine hv'.trans ?_
    congr 2
    have hu : ∀ i, ∃ u, unitIncl k u = t i := fun i => valuation_eq_one_iff.1 (ht i)
    choose u hu using hu
    have hdetu : ∀ a, GeneralLinearGroup.det (parahoricProj k (stdBlocks d hd) ⟨_, hpar⟩ a) =
        ∏ j : Fin (d a), unitRes k (u (stdBlocks d hd ⟨a, j⟩)) := by
      intro a
      ext
      rw [hdet a, Units.coe_prod]
      refine Finset.prod_congr rfl fun j _ => ?_
      have hx := (redK_eq_iff (k := k) ⟨_, hI.1⟩ (stdBlocks d hd ⟨a, j⟩) (stdBlocks d hd ⟨a, j⟩)
        (u (stdBlocks d hd ⟨a, j⟩) : 𝒪[k])).2 (by
          have h1 := congrArg Units.val (hu (stdBlocks d hd ⟨a, j⟩))
          simp only [val_diagT, diagonal_apply_eq]
          rw [← h1]
          simp only [unitIncl, Units.coe_map, MonoidHom.coe_coe]
          refine lt_of_eq_of_lt (congrArg (valuation k) (sub_eq_zero.2 rfl)) ?_
          simp)
      rw [hx]
      simp
    rw [torusChar_apply]
    simp_rw [hdetu, map_prod]
    rw [← (stdBlocks d hd).prod_comp, Fintype.prod_sigma]
    refine Finset.prod_congr rfl fun a _ => Finset.prod_congr rfl fun j _ => ?_
    have hb : blockOf d hd (stdBlocks d hd ⟨a, j⟩) = a := by simp [blockOf]
    rw [hb, ← hu]
    exact (hμ a _).symm

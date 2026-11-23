import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.ArchimedeanH0Cards.ContOfKer
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.ArchimedeanH0Cards.OdKill
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DegreeCountCohomology.PolZCases
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DegreeCountCohomology.AdicLC
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DegreeCountCohomology.FinAm

open Matrix Filter ReciprocityTheory.Gal UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa UpperTheory.V.Pa.B2

private theorem finite_cocycles_of_finite_H1 {A Γ : Type} [CommRing A] [Group Γ] [TopologicalSpace Γ] (M : FRep A Γ)
    (hH : Finite (H1 M.ρ)) : Finite (Z1 M.ρ) := by
  classical
  set N := Submodule.comap (Z1 M.ρ).subtype (B1 M.ρ) with hN
  have hB : Finite (B1 M.ρ) := by
    unfold B1
    exact Set.finite_range (d0 M.ρ) |>.to_subtype
  have hNf : Finite N := by
    refine Finite.of_injective (fun z : N => (⟨(z : Z1 M.ρ), z.2⟩ : B1 M.ρ)) ?_
    intro a b hab
    apply Subtype.ext
    apply Subtype.ext
    have := congrArg Subtype.val hab
    exact this
  have hQ : Finite ((Z1 M.ρ) ⧸ N.toAddSubgroup) := hH
  have hc := AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup N.toAddSubgroup
  apply Nat.finite_of_card_ne_zero
  rw [hc]
  exact Nat.mul_ne_zero Nat.card_pos.ne' Nat.card_pos.ne'

private def trRep {A Γ M N : Type} [CommRing A] [Group Γ] [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N]
    (ρ : Representation A Γ M) (e : M ≃ₗ[A] N) : Representation A Γ N where
  toFun g := e.toLinearMap ∘ₗ ρ g ∘ₗ e.symm.toLinearMap
  map_one' := by ext; simp
  map_mul' g h := by ext; simp

theorem UpperTheory.finite_selmerModule_of_finite_cohomology :
    ∀ (l : ℕ) [Fact l.Prime] (L : Loc) (G G0 : Glob l L) (h : G.Hom G0) (n : ℕ) (x : NP G0.frame n) (e : ℕ), FinH l G.Γ → (SelM h x (x.Am e)).Finite := by
  intro l _ L G G0 h n x e hF
  classical
  have hA := finAm l G0.frame n x e e
  haveI : Finite (x.Am e) := hA.1
  have ht : (algebraMap x.A (x.Am e)) x.t ^ e = 0 := hA.2.2.2.2.2.1
  obtain ⟨D, ⟨a⟩⟩ := odEx l L G G0 h n x (x.Am e) ⟨e, by rw [map_pow]; exact ht⟩
  have hK := odKill l L G G0 h n x (x.Am e) D a
  have hZ : Finite (Z1 D.M.ρ) := finite_cocycles_of_finite_H1 D.M (hF x.A D.M hK.1).1
  set rep := trRep D.M.ρ a.e with hrep
  have hrepv : ∀ g (Z : Od x.A (x.Am e) n x.a), rep g Z = a.e (D.M.ρ g (a.e.symm Z)) := by
    intro g Z
    rfl
  have hZl : Finite (Zl rep) := by
    refine Finite.of_injective (β := Z1 D.M.ρ)
      (fun y => ⟨fun g => a.e.symm (y.1 g), ⟨(y.2.1.comp a.e.symm).continuous, ?_⟩⟩) ?_
    · intro g k
      have := y.2.2 g k
      simp only [this, map_add, hrepv, LinearEquiv.symm_apply_apply]
    · intro y y' hyy
      apply Subtype.ext
      funext g
      have := congrFun (congrArg Subtype.val hyy) g
      exact a.e.symm.injective this
  have hAd : IsAd G.frame (fun g => x.ρX (x.Am e) (h.p₀ g)) (fun _ => (1 : x.Am e)) (Od x.A (x.Am e) n x.a) rep := by
    refine ⟨?_, ?_⟩
    · intro g Z
      rw [one_smul, hrepv, a.act]
      simp
    · intro Z
      rw [one_smul, hrepv, a.actc]
      simp
  have hP := (polZ l G.frame x.A (x.Am e) n (fun g => x.ρX (x.Am e) (h.p₀ g)) (fun _ => (1 : x.Am e))
    (Od x.A (x.Am e) n x.a) rep hAd).1
  refine (Set.finite_range (fun y : Zl rep => fun g : G.frame.G₀ => ((y.1 (g : G.Γ)) : Matrix (Fin n) (Fin n) (x.Am e)))).subset ?_
  intro z hz
  obtain ⟨hV, hC, hco, hcj, -, -⟩ := hz
  have hLC : IsLocallyConstant z := by
    have hij : ∀ i j, IsLocallyConstant fun g => z g i j := fun i j =>
      (adicLC _ _ _ e _ ht).1 (hC i j)
    rw [IsLocallyConstant.iff_isOpen_fiber]
    intro M
    have : z ⁻¹' {M} = ⋂ i, ⋂ j, (fun g => z g i j) ⁻¹' {M i j} := by
      ext g
      simp [Matrix.ext_iff.symm, funext_iff]
    rw [this]
    exact isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j => (hij i j).isOpen_fiber _
  obtain ⟨y, hy, -, hyz⟩ := hP z hV hLC (by intro g k; rw [one_smul]; exact hco g k)
    (by intro g; rw [one_smul]; exact hcj g)
  exact ⟨⟨y, hy⟩, funext hyz⟩

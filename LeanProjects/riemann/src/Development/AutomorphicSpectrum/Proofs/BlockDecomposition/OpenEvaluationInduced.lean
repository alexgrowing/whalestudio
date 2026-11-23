import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AvgVanish
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocallyConstantCompactSupportUnipotent
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WeylConjParabolicProjStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnipotentFactorizationCharacterTrivialStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntegralMulVecChangeModulusStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TwistedCoinvariantLeviActionStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CoinvariantUnipotentCharacterTrivialStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ModulusCharactersProductOneStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsOpenRightInvarianceOrbitCoefficientStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SupportCompactModParabolicOffClosedStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalSectionOpenCellAltBis
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OpenCellDoubleCosetUniquenessStatement

noncomputable section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.BZPhiPG
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.BZPhiPG.MemO

section
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem castM_cont {a b : ℕ} (e : a = b) : Continuous (castM k e) ∧ Continuous (castM k e).symm := by
  subst e
  exact ⟨continuous_id, continuous_id⟩

theorem exists_compact_cell (i t : ℕ) (C : Set (Mir k ((i + 1) + t + 1))) (hC : IsCompact C) (hCl : ∀ c ∈ C, c ∉ Cl k i t) :
    ∃ N : Set (Mir k ((i + 1) + t)), IsCompact N ∧ ∀ c ∈ C, ∃ h ∈ HPG k (i + 1) (t + 1), ∃ (d : Fin (t + 1) → k), ∃ m ∈ N,
      c = h * dEmb k i t d * wEl k i t * sEmb k ((i + 1) + t) m := by
  refine hC.induction_on (p := fun S => ∃ N : Set (Mir k ((i + 1) + t)), IsCompact N ∧ ∀ c ∈ S, ∃ h ∈ HPG k (i + 1) (t + 1),
    ∃ (d : Fin (t + 1) → k), ∃ m ∈ N, c = h * dEmb k i t d * wEl k i t * sEmb k ((i + 1) + t) m) ?_ ?_ ?_ ?_
  · exact ⟨∅, isCompact_empty, by simp⟩
  · rintro s t' hst ⟨N, hN, h⟩
    exact ⟨N, hN, fun c hc => h c (hst hc)⟩
  · rintro s t' ⟨N, hN, h⟩ ⟨N', hN', h'⟩
    refine ⟨N ∪ N', hN.union hN', ?_⟩
    rintro c (hc | hc)
    · obtain ⟨a, ha, d, m, hm, e⟩ := h c hc
      exact ⟨a, ha, d, m, Or.inl hm, e⟩
    · obtain ⟨a, ha, d, m, hm, e⟩ := h' c hc
      exact ⟨a, ha, d, m, Or.inr hm, e⟩
  · intro x hx
    obtain ⟨V, hV, μ, hμ, hs⟩ := GlobalTheory.T.exists_continuous_local_section_of_not_mem_Cl k i t x (hCl x hx)
    obtain ⟨V', hV', hcl, hsub⟩ := exists_mem_nhds_isClosed_subset hV
    refine ⟨C ∩ V', Filter.inter_mem self_mem_nhdsWithin (mem_nhdsWithin_of_mem_nhds hV'), μ '' (C ∩ V'), ?_, ?_⟩
    · exact (hC.inter_right hcl).image_of_continuousOn (hμ.mono (fun y hy => hsub hy.2))
    · intro c hc
      obtain ⟨a, ha, d, e⟩ := hs c (hsub hc.2)
      exact ⟨a, ha, d, μ c, ⟨c, hc, rfl⟩, e⟩
end

section
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem muD_fin (n : ℕ) : @MeasureTheory.IsFiniteMeasureOnCompacts (Fin n → k) (borel _) _ (muD k n) := by
  letI : MeasurableSpace (Fin n → k) := borel _
  haveI : BorelSpace (Fin n → k) := ⟨rfl⟩
  unfold muD
  infer_instance

theorem smInt_lin {n : ℕ} {W W' : Type} [AddCommGroup W] [Module ℂ W] [AddCommGroup W'] [Module ℂ W']
    (T : W →ₗ[ℂ] W') {F : (Fin n → k) → W} (l : IsLocallyConstant F) (c : HasCompactSupport F) :
    @GlobalTheory.CompanionTheory.Rodier.smInt _ _ (borel _) _ _ (muD k n) (T ∘ F) = T (@GlobalTheory.CompanionTheory.Rodier.smInt _ _ (borel _) _ _ (muD k n) F) := by
  letI : MeasurableSpace (Fin n → k) := borel _
  haveI : BorelSpace (Fin n → k) := ⟨rfl⟩
  haveI := muD_fin (k := k) n
  exact GlobalTheory.CompanionTheory.Rodier.SmIntEl.smInt_linear _ T l c

theorem smInt_zero' {n : ℕ} {W : Type} [AddCommGroup W] [Module ℂ W] :
    @GlobalTheory.CompanionTheory.Rodier.smInt _ _ (borel _) _ _ (muD k n) (fun _ => (0 : W)) = 0 := by
  unfold GlobalTheory.CompanionTheory.Rodier.smInt
  refine finsum_eq_zero_of_forall_eq_zero fun v => ?_
  by_cases hv : v = 0
  · rw [hv, smul_zero]
  · have : (fun _ : Fin n → k => (0 : W)) ⁻¹' {v} = ∅ := by
      ext x
      simp [Ne.symm hv]
    rw [this]
    simp

variable {i t : ℕ}

theorem eO_equiv (ψ : AddChar k Circle) (τ : MRep k (i + 1)) (σ : GRep k (t + 1)) (f : XS τ σ)
    (h : HPG k i (t + 1)) (m : Mir k (i + (t + 1))) :
    eO ψ f ((h : Mir k (i + (t + 1))) * m) = sigO τ σ ψ h (eO ψ f m) := by
  obtain ⟨hη, hproj⟩ := GlobalTheory.T.weyl_conj_parabolic_proj k i t h
  set a' := (pgProj k i (t + 1) h).1 with ha'
  set w' := (pgProj k i (t + 1) h).2 with hw'
  set y := wEl k i t * sEmb k ((i + 1) + t) (castM k (by omega) m) with hy
  set η := wEl k i t * sEmb k ((i + 1) + t) (castM k (by omega) (h : Mir k (i + (t + 1)))) * (wEl k i t)⁻¹ with hηd
  have e1 : wEl k i t * sEmb k ((i + 1) + t) (castM k (by omega) ((h : Mir k (i + (t + 1))) * m)) = η * y := by
    rw [map_mul, map_mul, hηd, hy]
    group
  let Tm : (phiN ψ τ).V ⊗[ℂ] σ.V →ₗ[ℂ] (phiN ψ τ).V ⊗[ℂ] σ.V :=
    extTensor (mtw (phiN ψ τ) (((t + 1 : ℕ) : ℝ) / 2)).ρ (σ.tw (-((i + 1 : ℕ) : ℝ) / 2)).ρ (a', w')
  let sc : ℂ := ((dpowM i (1 / 2) a' : ℂˣ) : ℂ) * ((dpow (t + 1) (-1 / 2) w' : ℂˣ) : ℂ)
  let G : (Fin (t + 1) → k) → (phiN ψ τ).V ⊗[ℂ] σ.V := fun d => qO τ σ ψ (evX f (dEmb k i t d * y))
  have hpt : ∀ d, qO τ σ ψ (evX f (dEmb k i t d * (η * y))) = (sc • Tm) (G ((w'⁻¹ : GL (Fin (t + 1)) k).1.mulVec d)) := by
    intro d
    obtain ⟨c, u, hc, hu, he⟩ := GlobalTheory.T.unipotent_factorization_character_trivial k ψ i t h d
    have e2 : dEmb k i t d * (η * y) =
        ((⟨η, hη⟩ : HPG k (i + 1) (t + 1)) : Mir k ((i + 1) + (t + 1))) * ((c : Mir k ((i + 1) + (t + 1))) *
          (dEmb k i t ((w'⁻¹ : GL (Fin (t + 1)) k).1.mulVec d) * y)) := by
      have he' : dEmb k i t d * η = η * (c : Mir k ((i + 1) + (t + 1))) * dEmb k i t ((w'⁻¹ : GL (Fin (t + 1)) k).1.mulVec d) := he
      calc dEmb k i t d * (η * y) = (dEmb k i t d * η) * y := (mul_assoc _ _ _).symm
        _ = (η * (c : Mir k ((i + 1) + (t + 1))) * dEmb k i t ((w'⁻¹ : GL (Fin (t + 1)) k).1.mulVec d)) * y := by rw [he']
        _ = _ := by rw [mul_assoc, mul_assoc]
    have e3 : ∀ (hh : HPG k (i + 1) (t + 1)) (x : Mir k ((i + 1) + (t + 1))),
        evX f ((hh : Mir k ((i + 1) + (t + 1))) * x) = sigX τ σ hh (evX f x) := fun hh x =>
      (f : smoothPart (ind (HPG k (i + 1) (t + 1)) (sigX τ σ))).1.2 hh x
    rw [e2, e3, e3]
    have e4 : ∀ (hh : HPG k (i + 1) (t + 1)) (v), sigX τ σ hh v =
        extTensor (mtw τ (((t + 1 : ℕ) : ℝ) / 2)).ρ (σ.tw (-((i + 1 + 1 : ℕ) : ℝ) / 2)).ρ (pgProj k (i + 1) (t + 1) hh) v := fun _ _ => rfl
    rw [e4, hproj, GlobalTheory.T.twisted_coinvariant_levi_action, e4, hc, GlobalTheory.T.coinvariant_unipotent_character_trivial k i t ψ τ σ u hu]
    rfl
  have hl := GlobalTheory.CompanionTheory.BZPhiPG.Fib.fibre_isLocallyConstant_hasCompactSupport k i t τ σ f y
  have hl2 := GlobalTheory.CompanionTheory.BZPhiPG.Fib.fibre_isLocallyConstant_hasCompactSupport k i t τ σ f (η * y)
  have hG : IsLocallyConstant G := hl.1.comp (qO τ σ ψ)
  have hGc : HasCompactSupport G := hl.2.comp_left (map_zero (qO τ σ ψ))
  have key : qO τ σ ψ (intO f (η * y)) =
      ((dpow (t + 1) 1 w' : ℂˣ) : ℂ) • (sc • Tm) (qO τ σ ψ (intO f y)) := by
    have s1 : qO τ σ ψ (intO f (η * y)) = @GlobalTheory.CompanionTheory.Rodier.smInt _ _ (borel _) _ _ (muD k (t + 1))
        (fun d => ((sc • Tm) ∘ G) ((w'⁻¹ : GL (Fin (t + 1)) k).1.mulVec d)) := by
      unfold intO
      rw [← smInt_lin (qO τ σ ψ) hl2.1 hl2.2]
      congr 1
      funext d
      exact hpt d
    have s2 : qO τ σ ψ (intO f y) = @GlobalTheory.CompanionTheory.Rodier.smInt _ _ (borel _) _ _ (muD k (t + 1)) G := by
      unfold intO
      rw [← smInt_lin (qO τ σ ψ) hl.1 hl.2]
      rfl
    rw [s1, GlobalTheory.T.integral_mulVec_change_modulus k (t + 1) _ w' ((sc • Tm) ∘ G) (hG.comp _) (hGc.comp_left (map_zero _)),
      smInt_lin (sc • Tm) hG hGc, s2]
  have e5 : sigO τ σ ψ h = Tm := rfl
  unfold eO
  rw [e1, ← hy, key, e5, map_smul, map_mul]
  have h6 : ((dpowM (i + (t + 1)) (-1 / 2) (h : Mir k (i + (t + 1))) : ℂˣ) : ℂ) * ((dpow (t + 1) 1 w' : ℂˣ) : ℂ) * sc = 1 := GlobalTheory.T.modulus_characters_product_one k i t h
  rw [LinearMap.smul_apply, smul_smul, smul_smul, Units.val_mul]
  congr 1
  linear_combination ((dpowM (i + (t + 1)) (-1 / 2) m : ℂˣ) : ℂ) * h6

theorem eO_supp (ψ : AddChar k Circle) (τ : MRep k (i + 1)) (σ : GRep k (t + 1)) (f : XS τ σ)
    (hf : ∀ x ∈ Cl k i t, evX f x = 0) :
    ∃ C : Set (Mir k (i + (t + 1))), IsCompact C ∧
      ∀ g, eO ψ f g ≠ 0 → ∃ h ∈ HPG k i (t + 1), ∃ c ∈ C, g = h * c := by
  have ee : i + (t + 1) = (i + 1) + t := by omega
  obtain ⟨C, hC, hCl, hsupp⟩ := GlobalTheory.T.support_compact_mod_parabolic_off_closed k i t τ σ f hf
  obtain ⟨N, hN, hcell⟩ := exists_compact_cell i t C hC hCl
  refine ⟨(castM k ee).symm '' N, hN.image (castM_cont ee).2, fun g hg => ?_⟩
  set y := wEl k i t * sEmb k ((i + 1) + t) (castM k ee g) with hy
  have hne : intO f y ≠ 0 := fun h0 => hg (by
    unfold eO
    rw [show wEl k i t * sEmb k ((i + 1) + t) (castM k (by omega) g) = y from rfl, h0, map_zero, smul_zero])
  obtain ⟨d, hd⟩ : ∃ d, evX f (dEmb k i t d * y) ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    apply hne
    unfold intO
    rw [show (fun d => evX f (dEmb k i t d * y)) = fun _ => 0 from funext hcon]
    exact smInt_zero'
  obtain ⟨h1, hh1, c, hc, e1⟩ := hsupp _ hd
  obtain ⟨h2, hh2, d2, m2, hm2, e2⟩ := hcell c hc
  have e3 : dEmb k i t d * wEl k i t * sEmb k ((i + 1) + t) (castM k ee g * m2⁻¹) =
      (h1 * h2) * dEmb k i t d2 * wEl k i t := by
    have e4 : dEmb k i t d * wEl k i t * sEmb k ((i + 1) + t) (castM k ee g) =
        h1 * (h2 * dEmb k i t d2 * wEl k i t * sEmb k ((i + 1) + t) m2) := by
      rw [← e2, ← e1, hy, mul_assoc]
    rw [map_mul, map_inv, ← mul_assoc, e4]
    group
  obtain ⟨h', hh', e5⟩ := GlobalTheory.T.open_cell_double_coset_uniqueness k i t _ d d2 (h1 * h2) (mul_mem hh1 hh2) e3
  refine ⟨h', hh', (castM k ee).symm m2, ⟨m2, hm2, rfl⟩, ?_⟩
  apply (castM k ee).injective
  rw [map_mul, MulEquiv.apply_symm_apply, e5]
  group

theorem memOAlt (i t : ℕ) (ψ : AddChar k Circle) (τ : MRep k (i + 1)) (σ : GRep k (t + 1)) (f : XS τ σ)
    (hf : ∀ x ∈ Cl k i t, evX f x = 0) :
    ∃ y : cIndSpace (HPG k i (t + 1)) (sigO τ σ ψ), (y : smoothPart (ind (HPG k i (t + 1)) (sigO τ σ ψ))).1.1 = eO ψ f := by
  let F : indSpace (HPG k i (t + 1)) (sigO τ σ ψ) := ⟨eO ψ f, fun h g => eO_equiv ψ τ σ f h g⟩
  have hF : F ∈ smoothPart (ind (HPG k i (t + 1)) (sigO τ σ ψ)) := by
    show IsOpen {g | ind (HPG k i (t + 1)) (sigO τ σ ψ) g F = F}
    convert GlobalTheory.T.isOpen_right_invariance_orbit_coefficient k i t ψ τ σ f using 1
    ext g
    simp only [Set.mem_setOf_eq]
    constructor
    · intro h m
      exact congrFun (congrArg Subtype.val h) m
    · intro h
      exact Subtype.ext (funext h)
  obtain ⟨C, hC, hs⟩ := eO_supp ψ τ σ f hf
  exact ⟨⟨⟨F, hF⟩, C, hC, hs⟩, rfl⟩
end

theorem eO_mem : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (i t : ℕ) (ψ : AddChar k Circle) (hψ : Continuous ψ) (τ : MRep k (i + 1)) (σ : GRep k (t + 1)) (hτ : IsSmooth τ.ρ) (hσ : IsSmooth σ.ρ) (f : XS τ σ) (hf : ∀ x ∈ Cl k i t, evX f x = 0),
  ∃ y : cIndSpace (HPG k i (t + 1)) (sigO τ σ ψ), (y : smoothPart (ind (HPG k i (t + 1)) (sigO τ σ ψ))).1.1 = eO ψ f := by
  intro k _ _ _ _ i t ψ _ τ σ _ _ f hf
  exact memOAlt i t ψ τ σ f hf

end GlobalTheory.CompanionTheory.BZPhiPG.MemO

end

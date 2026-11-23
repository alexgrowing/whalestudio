import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ImportsRestFurther
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FinCongMemLevEnv
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SurjectiveReductionOntoFiniteLevelGroup
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpecialUnitaryLiftInThetaGroupStatement
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.FWT GlobalTheory.CovTop
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.MassLink.StabLink

open IsDedekindDomain Matrix

section General

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem mem_hat_iff_swap {n : ℕ} (Λ : Submodule (𝓞 E) (Fin n → E)) (z : Fin n → FiniteAdeleRing (𝓞 F) F ⊗[F] E) :
    z ∈ GlobalTheory.AdLat.hat F (Λ : Set (Fin n → E)) ↔
      (fun i => Algebra.TensorProduct.comm F (FiniteAdeleRing (𝓞 F) F) E (z i)) ∈ Formalism.L2.Herm.hatL (F := F) Λ := by
  refine ⟨GlobalTheory.PrincInLevel.swap_mem_hatL Λ z, fun h => ?_⟩
  simpa only [AlgEquiv.symm_apply_apply] using GlobalTheory.PrincInLevel.swap_symm_mem_hat Λ _ h

theorem core {n r : ℕ} (h : n = r) (Λ : Submodule (𝓞 E) (Fin n → E))
    (β : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) (hF : Formalism.L2.DIV.IsFrame β Λ)
    (S K G : Matrix (Fin n) (Fin n) (FiniteAdeleRing (𝓞 F) F ⊗[F] E)) (hSK : S * K = G * S)
    (k : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F))
    (hk : k.val = K.map (Algebra.TensorProduct.comm F (FiniteAdeleRing (𝓞 F) F) E))
    (hkS : k ∈ Formalism.L2.DIV.St β) (s A : Matrix (Fin r) (Fin r) (FiniteAdeleRing (𝓞 F) F ⊗[F] E))
    (hs : S = s.submatrix (Fin.cast h) (Fin.cast h)) (hA : G = A.submatrix (Fin.cast h) (Fin.cast h)) :
    ∀ y ∈ GlobalTheory.AdLat.hat F ((Λ.comap (LinearMap.funLeft (𝓞 E) E (Fin.cast h)) : Submodule (𝓞 E) (Fin r → E)) :
        Set (Fin r → E)),
      ∃ y' ∈ GlobalTheory.AdLat.hat F ((Λ.comap (LinearMap.funLeft (𝓞 E) E (Fin.cast h)) : Submodule (𝓞 E) (Fin r → E)) :
        Set (Fin r → E)), A *ᵥ (s *ᵥ y) = s *ᵥ y' := by
  subst h
  have e : Λ.comap (LinearMap.funLeft (𝓞 E) E (Fin.cast (rfl : n = n))) = Λ := by
    ext x
    simp only [Submodule.mem_comap, Fin.cast_refl]
    exact Iff.rfl
  simp only [Fin.cast_refl, submatrix_id_id] at hs hA
  subst hs hA
  rw [e]
  intro y hy
  refine ⟨K *ᵥ y, ?_, ?_⟩
  · rw [mem_hat_iff_swap] at hy ⊢
    have h1 := (GlobalTheory.SeeMatchOnto.mem_hatL_iff_of_St hF hkS _).1 hy
    convert h1 using 1
    funext i
    rw [hk]
    exact RingHom.map_mulVec (Algebra.TensorProduct.comm F (FiniteAdeleRing (𝓞 F) F) E).toRingHom K y i
  · rw [mulVec_mulVec, mulVec_mulVec, hSK]

end General

end GlobalTheory.MassLink.StabLink

namespace GlobalTheory.MassLink.StabLink

open IsDedekindDomain Matrix Formalism.L2.Theta Formalism.BasicNotions.TH

theorem inclAF_injective (D : D7) :
    Function.Injective (GlobalTheoryTheory.GenusMassVolumes.inclR (F := D.host.F) (E := D.host.E) (GlobalTheoryTheory.GenusMassVolumes.AF D.host.F)) :=
  Algebra.TensorProduct.includeRight_injective (NumberField.AdeleRing.algebraMap_injective (𝓞 D.host.F) D.host.F)

theorem mem_UJ_of_GQ (D : D7) (V : HSp D) (g : GA D V) (γ : GL (Fin V.rank) D.host.E) (hg : g ∈ GQ V)
    (hm : matHom V g = Formalism.UG.bc (GlobalTheoryTheory.GenusMassVolumes.inclR (GlobalTheoryTheory.GenusMassVolumes.AF D.host.F)) γ) :
    γ ∈ Formalism.UG.UJ (D.sp.cm.sig : D.host.E →+* D.host.E) V.gram := by
  have h1 : matHom V g ∈ GlobalTheoryTheory.GenusMassVolumes.HFin (GlobalTheoryTheory.GenusMassVolumes.AF D.host.F) D.sp.cm.sig V.gram := hg
  obtain ⟨x, hx, e⟩ := Subgroup.mem_map.1 h1
  have e2 : Formalism.UG.bc (GlobalTheoryTheory.GenusMassVolumes.inclR (GlobalTheoryTheory.GenusMassVolumes.AF D.host.F)) x =
      Formalism.UG.bc (GlobalTheoryTheory.GenusMassVolumes.inclR (GlobalTheoryTheory.GenusMassVolumes.AF D.host.F)) γ := e.trans hm
  have : x = γ := by
    refine Units.ext (Matrix.ext fun a b => inclAF_injective D ?_)
    have := congrArg (fun M : GL (Fin V.rank) (GlobalTheoryTheory.GenusMassVolumes.AF D.host.F ⊗[D.host.F] D.host.E) =>
      M.1 a b) e2
    simpa [Formalism.UG.bc] using this
  exact this ▸ hx

theorem finHom_val_of_mat (D : D7) (V : HSp D) (g : GA D V) (γ : GL (Fin V.rank) D.host.E)
    (hm : matHom V g = Formalism.UG.bc (GlobalTheoryTheory.GenusMassVolumes.inclR (GlobalTheoryTheory.GenusMassVolumes.AF D.host.F)) γ) :
    (finHom V g).val = (γ : Matrix (Fin V.rank) (Fin V.rank) D.host.E).map
      (fun x => (1 : FiniteAdeleRing (𝓞 D.host.F) D.host.F) ⊗ₜ[D.host.F] x) := by
  have : (finHom V g).val = ((matHom V g).val).map
      (Algebra.TensorProduct.map (GlobalTheoryTheory.GenusMassVolumes.sndA D.host.F) (AlgHom.id D.host.F D.host.E)) := rfl
  rw [this, hm]
  ext a b
  simp [Formalism.UG.bc, GlobalTheoryTheory.GenusMassVolumes.inclR, Algebra.TensorProduct.map_tmul]

example (D : D7) (x : D.host.E) : letI : IsCMField D.host.E := D.host.isCMField_hostE;
    D.sp.cm.sig x = IsCMField.complexConj D.host.E x := rfl

end GlobalTheory.MassLink.StabLink

namespace GlobalTheory.MassLink.StabLink

open IsDedekindDomain Matrix Formalism.L2.Theta Formalism.BasicNotions.TH

section Herm

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem herm_transpose {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (x y : Fin n → E) :
    ReciprocityTheory.ChartRestriction.G.FD.herm Jᵀ x y =
      (fun b => (IsCMField.complexConj E : E →+* E) (y b)) ⬝ᵥ (J *ᵥ x) := by
  simp only [ReciprocityTheory.ChartRestriction.G.FD.herm, ReciprocityTheory.ChartRestriction.G.FD.cc, dotProduct, mulVec, transpose_apply, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun a _ => ?_
  simp only [AlgEquiv.toRingEquiv_eq_coe, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe, AlgEquiv.coe_ringEquiv]
  ring

theorem herm_unitary {n r : ℕ} (h : n = r) (J γ : Matrix (Fin n) (Fin n) E)
    (hγ : Formalism.UG.cT (IsCMField.complexConj E : E →+* E) γ * J * γ = J) (x y : Fin r → E) :
    ReciprocityTheory.ChartRestriction.G.FD.herm (J.submatrix (Fin.cast h.symm) (Fin.cast h.symm))ᵀ
        (γ.submatrix (Fin.cast h.symm) (Fin.cast h.symm) *ᵥ x) (γ.submatrix (Fin.cast h.symm) (Fin.cast h.symm) *ᵥ y) =
      ReciprocityTheory.ChartRestriction.G.FD.herm (J.submatrix (Fin.cast h.symm) (Fin.cast h.symm))ᵀ x y := by
  subst h
  simp only [Fin.cast_refl, submatrix_id_id]
  rw [herm_transpose, herm_transpose]
  have key : (fun b => (IsCMField.complexConj E : E →+* E) ((γ *ᵥ y) b)) =
      γ.map (IsCMField.complexConj E : E →+* E) *ᵥ (fun b => (IsCMField.complexConj E : E →+* E) (y b)) := by
    funext b
    simp only [mulVec, dotProduct, map_sum, map_mul, Matrix.map_apply]
  rw [key, dotProduct_comm, dotProduct_mulVec, ← mulVec_transpose, dotProduct_comm, mulVec_mulVec, mulVec_mulVec]
  have hγ' : (γ.map (IsCMField.complexConj E : E →+* E))ᵀ * J * γ = J := hγ
  rw [hγ']

end Herm

end GlobalTheory.MassLink.StabLink

namespace GlobalTheory.MassLink.StabLink

open IsDedekindDomain Matrix Formalism.L2.Theta Formalism.BasicNotions.TH

theorem fwd (D : D7) (Tu : Type) (Cl : LevCh D Tu) (t0 : Tu) (hCl : Cl.Is t0) (i : Fin D.R.m)
    (s : Matrix (Fin D.R.r) (Fin D.R.r) (GlobalTheory.AdLat.RA (maximalRealSubfield D.host.E) D.host.E))
    (hlift : ((finHom (Wc D i) (GlobalTheory.MassLink.lift D i s)).val :
        Matrix (Fin (Wc D i).rank) (Fin (Wc D i).rank) (GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E)) =
      s.submatrix (Fin.cast (rank_Wc i)) (Fin.cast (rank_Wc i)))
    (g : GA D (Wc D i)) (γ : GL (Fin (Wc D i).rank) D.host.E) (γr : GL (Fin D.R.r) D.host.E)
    (hm : matHom (Wc D i) g = Formalism.UG.bc (GlobalTheoryTheory.GenusMassVolumes.inclR (GlobalTheoryTheory.GenusMassVolumes.AF D.host.F)) γ)
    (hγr : (γ : Matrix (Fin (Wc D i).rank) (Fin (Wc D i).rank) D.host.E).submatrix (Fin.cast (rank_Wc i).symm)
      (Fin.cast (rank_Wc i).symm) = (γr : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E))
    (hk : Formalism.IndefR.Lev.finE (Wc D i) ((GlobalTheory.MassLink.lift D i s)⁻¹ * g * GlobalTheory.MassLink.lift D i s) ∈
      GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.levW Cl i (LevelP.full Cl.Pg D.R.r ℂ)) :
    ∀ y ∈ GlobalTheory.AdLat.hat (maximalRealSubfield D.host.E) (GlobalTheory.MassLink.lat Cl i : Set (Fin D.R.r → D.host.E)),
      ∃ y' ∈ GlobalTheory.AdLat.hat (maximalRealSubfield D.host.E) (GlobalTheory.MassLink.lat Cl i : Set (Fin D.R.r → D.host.E)),
        GlobalTheory.UCls.ratM (maximalRealSubfield D.host.E) (γr : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E) *ᵥ (s *ᵥ y) =
          s *ᵥ y' := by
  obtain ⟨c, hc⟩ := hCl.βW i
  set h := GlobalTheory.MassLink.lift D i s with hh
  have hSK : (finHom (Wc D i) h).val * (finHom (Wc D i) (h⁻¹ * g * h)).val =
      (finHom (Wc D i) g).val * (finHom (Wc D i) h).val := by
    rw [← Units.val_mul, ← Units.val_mul, ← map_mul, ← map_mul]
    congr 2
    group
  have hA : (finHom (Wc D i) g).val = (GlobalTheory.UCls.ratM (maximalRealSubfield D.host.E)
      (γr : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E)).submatrix (Fin.cast (rank_Wc i)) (Fin.cast (rank_Wc i)) := by
    rw [finHom_val_of_mat D (Wc D i) g γ hm, ← hγr]
    ext a b
    simp [GlobalTheory.UCls.ratM]
  exact core (F := D.host.F) (rank_Wc i) (Cl.ΛW i) (Cl.βW i) hc.1 _ _ _ hSK
    (Formalism.IndefR.Lev.finE (Wc D i) (h⁻¹ * g * h)) rfl (Formalism.L2.DIV.parLev_St (Formalism.L2.DIV.lev_le_parLev hk)) s _
    hlift hA

end GlobalTheory.MassLink.StabLink

namespace GlobalTheory.MassLink.StabLink

open IsDedekindDomain Matrix Formalism.L2.Theta Formalism.BasicNotions.TH

theorem ratStab_of_lift : ∀ (D : D7) (Tu : Type) (Cl : LevCh D Tu) (t0 : Tu), Cl.Is t0 → ∀ (i : Fin D.R.m),
    letI : IsCMField D.host.E := D.host.isCMField_hostE;
    ∀ (s : Matrix (Fin D.R.r) (Fin D.R.r) (GlobalTheory.AdLat.RA (maximalRealSubfield D.host.E) D.host.E)),
    ((finHom (Wc D i) (GlobalTheory.MassLink.lift D i s)).val :
        Matrix (Fin (Wc D i).rank) (Fin (Wc D i).rank) (GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E)) =
      s.submatrix (Fin.cast (rank_Wc i)) (Fin.cast (rank_Wc i)) →
    ∀ (g : GA D (Wc D i)) (γ : GL (Fin (Wc D i).rank) D.host.E) (γr : GL (Fin D.R.r) D.host.E),
    g ∈ GQ (Wc D i) → matHom (Wc D i) g = Formalism.UG.bc (GlobalTheoryTheory.GenusMassVolumes.inclR (GlobalTheoryTheory.GenusMassVolumes.AF D.host.F)) γ →
    (γ : Matrix (Fin (Wc D i).rank) (Fin (Wc D i).rank) D.host.E).submatrix (Fin.cast (rank_Wc i).symm)
      (Fin.cast (rank_Wc i).symm) = (γr : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E) →
    (γr : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).det = 1 →
    Formalism.IndefR.Lev.finE (Wc D i) ((GlobalTheory.MassLink.lift D i s)⁻¹ * g * GlobalTheory.MassLink.lift D i s) ∈
      GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.levW Cl i (LevelP.full Cl.Pg D.R.r ℂ) →
    γr ∈ GlobalTheory.SUVol.ratStab (GlobalTheory.MassLink.gm D i) (GlobalTheory.MassLink.lat Cl i : Set (Fin D.R.r → D.host.E)) s := by
  intro D Tu Cl t0 hCl i s hlift g γ γr hg hm hγr hdet hk
  refine ⟨hdet, fun x y => ?_, fun x => ?_⟩
  · have hU := mem_UJ_of_GQ D (Wc D i) g γ hg hm
    have := herm_unitary (rank_Wc i) (Wc D i).gram (γ : Matrix (Fin (Wc D i).rank) (Fin (Wc D i).rank) D.host.E)
      hU x y
    rw [hγr] at this
    exact this
  · have hm' : matHom (Wc D i) g⁻¹ = Formalism.UG.bc (GlobalTheoryTheory.GenusMassVolumes.inclR (GlobalTheoryTheory.GenusMassVolumes.AF D.host.F)) γ⁻¹ := by
      rw [map_inv, hm, map_inv]
    have hγr' : ((γ⁻¹ : GL (Fin (Wc D i).rank) D.host.E) : Matrix (Fin (Wc D i).rank) (Fin (Wc D i).rank) D.host.E).submatrix
        (Fin.cast (rank_Wc i).symm) (Fin.cast (rank_Wc i).symm) =
        ((γr⁻¹ : GL (Fin D.R.r) D.host.E) : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E) := by
      rw [Matrix.coe_units_inv, Matrix.coe_units_inv, ← hγr]
      exact (Matrix.inv_submatrix_equiv _ (finCongr (rank_Wc i).symm) (finCongr (rank_Wc i).symm)).symm
    have hk' : Formalism.IndefR.Lev.finE (Wc D i) ((GlobalTheory.MassLink.lift D i s)⁻¹ * g⁻¹ * GlobalTheory.MassLink.lift D i s) ∈
        GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.levW Cl i (LevelP.full Cl.Pg D.R.r ℂ) := by
      have e : (GlobalTheory.MassLink.lift D i s)⁻¹ * g⁻¹ * GlobalTheory.MassLink.lift D i s =
          ((GlobalTheory.MassLink.lift D i s)⁻¹ * g * GlobalTheory.MassLink.lift D i s)⁻¹ := by group
      rw [e, map_inv]
      exact inv_mem hk
    constructor
    · rintro ⟨y, hy, hxy⟩
      obtain ⟨y', hy', e⟩ := fwd D Tu Cl t0 hCl i s hlift g⁻¹ γ⁻¹ γr⁻¹ hm' hγr' hk' y hy
      refine ⟨y', hy', ?_⟩
      rw [← e, hxy, mulVec_mulVec, ← GlobalTheory.SUVol.ratM_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one,
        GlobalTheory.SUVol.ratM_one, one_mulVec]
    · rintro ⟨y, hy, rfl⟩
      obtain ⟨y', hy', e⟩ := fwd D Tu Cl t0 hCl i s hlift g γ γr hm hγr hk y hy
      exact ⟨y', hy', e.symm⟩

end GlobalTheory.MassLink.StabLink

namespace GlobalTheory.MassLink.StabLink

open IsDedekindDomain Matrix Formalism.L2.Theta Formalism.BasicNotions.TH

theorem ratStab_mem : ∀ (D : D7) (Tu : Type) (Cl : LevCh D Tu) (t0 : Tu), Cl.Is t0 → ∀ (i : Fin D.R.m),
    letI : IsCMField D.host.E := D.host.isCMField_hostE;
    ∀ (s : Matrix (Fin D.R.r) (Fin D.R.r) (GlobalTheory.AdLat.RA (maximalRealSubfield D.host.E) D.host.E)),
    GlobalTheory.SUVol.IsSA (GlobalTheory.MassLink.gm D i) s →
    ∀ (g : Theta.GA D (Wc D i)) (γ : GL (Fin (Wc D i).rank) D.host.E) (γr : GL (Fin D.R.r) D.host.E),
    g ∈ Theta.GQ (Wc D i) → Theta.matHom (Wc D i) g = Formalism.UG.bc (GlobalTheoryTheory.GenusMassVolumes.inclR (GlobalTheoryTheory.GenusMassVolumes.AF D.host.F)) γ →
    (γ : Matrix (Fin (Wc D i).rank) (Fin (Wc D i).rank) D.host.E).submatrix (Fin.cast (rank_Wc i).symm)
      (Fin.cast (rank_Wc i).symm) = (γr : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E) →
    (γr : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).det = 1 →
    Formalism.IndefR.Lev.finE (Wc D i) ((GlobalTheory.MassLink.lift D i s)⁻¹ * g * GlobalTheory.MassLink.lift D i s) ∈
      GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.levW Cl i (LevelP.full Cl.Pg D.R.r ℂ) →
    γr ∈ GlobalTheory.SUVol.ratStab (GlobalTheory.MassLink.gm D i) (GlobalTheory.MassLink.lat Cl i : Set (Fin D.R.r → D.host.E)) s := by
  intro D Tu Cl t0 hCl i s hs
  exact ratStab_of_lift D Tu Cl t0 hCl i s (GlobalTheory.T.special_unitary_lift_in_theta_group D i s hs).2

end GlobalTheory.MassLink.StabLink

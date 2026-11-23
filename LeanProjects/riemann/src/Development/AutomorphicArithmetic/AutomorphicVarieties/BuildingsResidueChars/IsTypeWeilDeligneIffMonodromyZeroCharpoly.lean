import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.CoefficientRepTrivialOnUnramified
import Formalism.SharpRestriction.LevelLetterCocycles.ExistsInertiaCharpolyFactorOfTameType

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial GlobalTheory.CuspRep GlobalTheory.WeilDeligne UpperTheory.V.Hi
open UpperTheory.V.W (Plc)
open Formalism.MainNotions.N (IsSSRep IsInv)
open scoped Matrix

private noncomputable def diagRep {G : Type} [Group G] {n : ℕ} (χ : Fin n → G →* ℂˣ) : G →* GL (Fin n) ℂ :=
  (Units.map (Matrix.diagonalRingHom (Fin n) ℂ).toMonoidHom).comp
    ((MulEquiv.piUnits (M := fun _ : Fin n => ℂ)).symm.toMonoidHom.comp (MonoidHom.pi χ))

private theorem commute_of_semisimple_of_charpoly_prod_chars {G : Type} [Group G] {m n : ℕ} (T : G →* Module.End ℂ (Fin m → ℂ))
    (χ : Fin n → G →* ℂˣ) (hss : ∀ g, (T g).IsSemisimple)
    (hcp : ∀ g, (T g).charpoly = ∏ i, (X - C ((χ i g : ℂˣ) : ℂ))) (g k : G) :
    Commute (T g) (T k) := by
  have hone : T (g * k * g⁻¹ * k⁻¹) = 1 := by
    have h1 : (T (g * k * g⁻¹ * k⁻¹)).charpoly = (X - C (1 : ℂ)) ^ n := by
      rw [hcp]
      have : ∀ i, ((χ i (g * k * g⁻¹ * k⁻¹) : ℂˣ) : ℂ) = 1 := by
        intro i
        simp [map_mul, map_inv, mul_comm, mul_left_comm, mul_assoc]
      simp [this]
    have hdvd : minpoly ℂ (T (g * k * g⁻¹ * k⁻¹)) ∣ (X - C (1 : ℂ)) ^ n :=
      h1 ▸ LinearMap.minpoly_dvd_charpoly _
    have hd : minpoly ℂ (T (g * k * g⁻¹ * k⁻¹)) ∣ X - C (1 : ℂ) := by
      rcases Nat.eq_zero_or_pos n with hn | hn
      · subst hn
        exact dvd_trans (by simpa using hdvd) (one_dvd _)
      · exact ((hss _).minpoly_squarefree.dvd_pow_iff_dvd hn.ne').mp hdvd
    have := (minpoly.dvd_iff).mp hd
    simpa [sub_eq_zero] using this
  have hgk : g * k = (g * k * g⁻¹ * k⁻¹) * (k * g) := by group
  have h2 : T (g * k) = T (g * k * g⁻¹ * k⁻¹) * T (k * g) := by
    rw [← map_mul, ← hgk]
  rw [hone, one_mul, map_mul, map_mul] at h2
  exact h2

private theorem exists_basis_eigen_of_semisimple_commuting {G : Type} [Group G] {m : ℕ} (T : G →* Module.End ℂ (Fin m → ℂ))
    (hss : ∀ g, (T g).IsSemisimple) (hc : ∀ g k, Commute (T g) (T k)) :
    ∃ (b : Module.Basis (Fin m) ℂ (Fin m → ℂ)) (c : Fin m → G → ℂ), ∀ j g, T g (b j) = c j g • b j := by
  classical
  let A : (G → ℂ) → Submodule ℂ (Fin m → ℂ) := fun φ => ⨅ g, (T g).maxGenEigenspace (φ g)
  have hmaps : ∀ (g k : G) (μ : ℂ), Set.MapsTo (T g) ((T k).maxGenEigenspace μ) ((T k).maxGenEigenspace μ) :=
    fun g k μ => Module.End.mapsTo_maxGenEigenspace_of_comm (hc k g) μ
  have hind : iSupIndep A :=
    Module.End.independent_iInf_maxGenEigenspace_of_forall_mapsTo (fun g => T g) hmaps
  have htop : iSup A = ⊤ :=
    Module.End.iSup_iInf_maxGenEigenspace_eq_top_of_forall_mapsTo (fun g => T g) hmaps
      (fun g => Module.End.iSup_maxGenEigenspace_eq_top _)
  have hint : DirectSum.IsInternal A := DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top hind htop
  let v : (φ : G → ℂ) → Module.Basis (Module.Free.ChooseBasisIndex ℂ (A φ)) ℂ (A φ) :=
    fun φ => Module.Free.chooseBasis ℂ (A φ)
  let b0 := hint.collectedBasis v
  let e := b0.indexEquiv (Pi.basisFun ℂ (Fin m))
  refine ⟨b0.reindex e, fun j => (e.symm j).1, fun j g => ?_⟩
  have hmem : b0 (e.symm j) ∈ A (e.symm j).1 := hint.collectedBasis_mem v _
  have hmem' : b0 (e.symm j) ∈ (T g).eigenspace ((e.symm j).1 g) := by
    have := (Submodule.mem_iInf _).mp hmem g
    rwa [(hss g).isFinitelySemisimple.maxGenEigenspace_eq_eigenspace] at this
  rw [Module.Basis.reindex_apply]
  exact Module.End.mem_eigenspace_iff.mp hmem'

private theorem exists_linearEquiv_diagonal_chars_of_eigenbasis {G : Type} [Group G] {m n : ℕ} (T : G →* Module.End ℂ (Fin m → ℂ)) (χ : Fin n → G →* ℂˣ)
    (hcp : ∀ g, (T g).charpoly = ∏ i, (X - C ((χ i g : ℂˣ) : ℂ)))
    (b : Module.Basis (Fin m) ℂ (Fin m → ℂ)) (c : Fin m → G → ℂ) (hT : ∀ j g, T g (b j) = c j g • b j) :
    ∃ e : (Fin m → ℂ) ≃ₗ[ℂ] (Fin n → ℂ),
      ∀ g v, e (T g v) = Matrix.toLin' (Matrix.diagonal fun i => ((χ i g : ℂˣ) : ℂ)) (e v) := by
  classical
  have hinj : ∀ j, Function.Injective fun z : ℂ => z • b j := fun j => smul_left_injective ℂ (b.ne_zero j)
  have hone : ∀ j, c j 1 = 1 := by
    intro j
    apply hinj j
    simp only
    rw [← hT, map_one, one_smul]
    rfl
  have hmul : ∀ j g k, c j (g * k) = c j g * c j k := by
    intro j g k
    apply hinj j
    simp only
    rw [← hT, map_mul, Module.End.mul_apply, hT, map_smul, hT, smul_smul, mul_comm]
  let ψ : Fin m → (G →* ℂ) := fun j => ⟨⟨c j, hone j⟩, hmul j⟩
  let χ' : Fin n → (G →* ℂ) := fun i => (Units.coeHom ℂ).comp (χ i)
  have hroots : ∀ {k : ℕ} (d : Fin k → ℂ), (∏ j, (X - C (d j))).roots = Finset.univ.val.map d := by
    intro k d
    rw [Finset.prod_eq_multiset_prod,
      show Finset.univ.val.map (fun j => X - C (d j)) = (Finset.univ.val.map d).map (fun a => X - C a) by
        rw [Multiset.map_map]; rfl, Polynomial.roots_multiset_prod_X_sub_C]
  have hdiag : ∀ g, LinearMap.toMatrix b b (T g) = Matrix.diagonal fun j => c j g := by
    intro g
    ext i j
    rw [LinearMap.toMatrix_apply, hT, map_smul, b.repr_self, Matrix.diagonal_apply]
    by_cases h : i = j
    · subst h; simp
    · simp [Finsupp.single_apply, Ne.symm h, h]
  have hsum : ∀ g, ∑ j, c j g = ∑ i, ((χ i g : ℂˣ) : ℂ) := by
    intro g
    have hp := LinearMap.charpoly_toMatrix (T g) b
    rw [hdiag, Matrix.charpoly_diagonal, hcp] at hp
    have := congrArg (fun p => p.roots.sum) hp
    simpa [hroots, Finset.sum_eq_multiset_sum] using this
  have hcount : ∀ φ : G →* ℂ,
      Fintype.card {j // ψ j = φ} = Fintype.card {i // χ' i = φ} := by
    intro φ
    have hli := linearIndependent_monoidHom G ℂ
    set l : (G →* ℂ) →₀ ℂ := ∑ j, Finsupp.single (ψ j) 1 - ∑ i, Finsupp.single (χ' i) 1 with hl
    have hlc : Finsupp.linearCombination ℂ (fun f : G →* ℂ => (f : G → ℂ)) l = 0 := by
      rw [hl, map_sub, map_sum, map_sum]
      simp only [Finsupp.linearCombination_single, one_smul]
      funext g
      simp only [Pi.sub_apply, Finset.sum_apply, Pi.zero_apply]
      have := hsum g
      simp only [ψ, χ', MonoidHom.coe_mk, OneHom.coe_mk, MonoidHom.coe_comp, Function.comp_apply,
        Units.coeHom_apply]
      rw [this, sub_self]
    have hl0 : l = 0 := linearIndependent_iff.mp hli l hlc
    have hφ := congrArg (fun f => f φ) hl0
    simp only [hl, Finsupp.sub_apply, Finsupp.finset_sum_apply, Finsupp.single_apply,
      Finsupp.coe_zero, Pi.zero_apply, Finset.sum_boole, sub_eq_zero] at hφ
    rw [Fintype.card_subtype, Fintype.card_subtype]
    exact_mod_cast hφ
  let π : Fin m ≃ Fin n := Equiv.ofFiberEquiv (f := ψ) (g := χ') fun φ => Fintype.equivOfCardEq (hcount φ)
  have hπ : ∀ j, χ' (π j) = ψ j := fun j => Equiv.ofFiberEquiv_map _ j
  have hcoord : ∀ g v k, b.repr (T g v) k = c k g * b.repr v k := by
    intro g v k
    have := b.ext (f₁ := (Finsupp.lapply k).comp (b.repr.toLinearMap.comp (T g)))
      (f₂ := c k g • (Finsupp.lapply k).comp b.repr.toLinearMap) (by
        intro j
        simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, hT, map_smul, b.repr_self,
          Finsupp.lapply_apply, LinearMap.smul_apply, Finsupp.smul_apply, Finsupp.single_apply, smul_eq_mul]
        by_cases h : j = k
        · subst h; simp
        · simp [h])
    simpa using LinearMap.congr_fun this v
  refine ⟨b.equivFun.trans (LinearEquiv.funCongrLeft ℂ ℂ π.symm), fun g v => ?_⟩
  ext i
  simp only [LinearEquiv.trans_apply, LinearEquiv.funCongrLeft_apply, LinearMap.funLeft_apply,
    Module.Basis.equivFun_apply, Matrix.toLin'_apply, Matrix.mulVec_diagonal, hcoord]
  congr 1
  have h1 := hπ (π.symm i)
  rw [Equiv.apply_symm_apply] at h1
  have h2 := congrArg (fun f : G →* ℂ => f g) h1
  simpa [ψ, χ'] using h2.symm

theorem UpperTheory.isTypeWeilDeligne_iff_monodromy_zero_charpoly :
    ∀ (L Ω : Type) [Field L] [NumberField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (n : ℕ) (w : Plc L) (A : ValuationSubring Ω) (h : IsPlaceOver A w) (χ : Fin n → Ine (F := L) A →* ℂˣ) (x : WD h), IsTypeWD h χ x ↔ x.mono0 ∧ ∀ s, x.charPol (ineIncl h s) = ∏ i, (X - C (χ i s : ℂ)) := by
  intro L Ω _ _ _ _ _ n w A h χ x
  constructor
  · rintro ⟨b, rfl, hN, hb⟩
    refine ⟨(WD.monodromyZero_ofWeilDeligneRepClass_iff b).mpr hN, fun s => ?_⟩
    rw [WD.charPol_mk, hb, Matrix.charpoly_toLin', Matrix.charpoly_diagonal]
  · rintro ⟨h0, hc⟩
    obtain ⟨m, a, rfl⟩ := WD.exists_rep x
    rw [WD.monodromyZero_ofWeilDeligneRepClass_iff] at h0
    let T : ↥(Ine (F := L) A) →* Module.End ℂ (Fin m → ℂ) := a.ρ.comp (ineIncl h)
    have hss : ∀ g, (T g).IsSemisimple := fun g => a.semisimple _
    have hcp : ∀ g, (T g).charpoly = ∏ i, (X - C ((χ i g : ℂˣ) : ℂ)) := by
      intro g
      have := hc g
      rwa [WD.charPol_mk] at this
    obtain ⟨bs, c, hT⟩ := exists_basis_eigen_of_semisimple_commuting T hss (commute_of_semisimple_of_charpoly_prod_chars T χ hss hcp)
    obtain ⟨e, he⟩ := exists_linearEquiv_diagonal_chars_of_eigenbasis T χ hcp bs c hT
    refine ⟨a.transport e, ?_, ?_, ?_⟩
    · refine (WD.sound ⟨e, fun σ v => ?_, fun v => ?_⟩).symm
      · simp [WDRep.transport]
      · simp [WDRep.transport]
    · simp [WDRep.transport, h0]
    · intro s
      apply LinearMap.ext
      intro u
      have := he s (e.symm u)
      simp only [LinearEquiv.apply_symm_apply] at this
      rw [← this]
      simp [WDRep.transport, T]

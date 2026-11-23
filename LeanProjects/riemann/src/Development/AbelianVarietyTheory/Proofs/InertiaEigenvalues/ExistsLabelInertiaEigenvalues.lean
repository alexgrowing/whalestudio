import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.CoeffRingsHaveRootsOfUnity
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsOpenSubgroup
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.RootsCharpolyPowEqMapPow
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EqOneOfPowEqOneOfCharpoly

noncomputable section

namespace GlobalTheory.PendOf.LabIneAll

open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.L2 NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module
open Polynomial GlobalTheory.Pass GlobalTheory.PendOf GlobalTheory.WeilDeligne

section Alg

theorem charpoly_pow_of_prod {K ι : Type} [Field K] [IsAlgClosed K] {r : ℕ} (A : Matrix (Fin r) (Fin r) K)
    (s : Multiset ι) (f : ι → K) (h : A.charpoly = (s.map fun x => X - C (f x)).prod) (n : ℕ) :
    (A ^ n).charpoly = (s.map fun x => X - C (f x ^ n)).prod := by
  have h1 : A.charpoly.roots = s.map f := by
    rw [h, ← roots_multiset_prod_X_sub_C (s.map f), Multiset.map_map]
    rfl
  have h2 := GlobalTheory.CharpolyPow.roots_charpoly_pow K r n A
  rw [(IsAlgClosed.splits (A ^ n).charpoly).eq_prod_roots_of_monic (Matrix.charpoly_monic _), h2, h1,
    Multiset.map_map, Multiset.map_map]
  rfl

theorem teich_zero {g : ℕ} [Fact g.Prime] (t : Formalism.CyclotomicNorms.Fbar g →* ℂ)
    (ht : ∀ x y, x ≠ 0 → y ≠ 0 → t x = t y → x = y) : t 0 = 0 := by
  classical
  obtain ⟨x, hx⟩ := Infinite.exists_notMem_finset ({0, 1} : Finset (Formalism.CyclotomicNorms.Fbar g))
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hx
  by_contra h0
  have h1 : t 0 * t x = t 0 * t 1 := by rw [← map_mul, ← map_mul, zero_mul, zero_mul]
  exact hx.2 (ht x 1 hx.1 one_ne_zero (mul_left_cancel₀ h0 h1))

end Alg

section Local

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
variable {A : ValuationSubring Ω}

theorem mem_of_isOpen {H : Subgroup (Ine (F := E) A)} (hH : IsOpen (H : Set (Ine (F := E) A)))
    {γ : G E Ω} (hγ : TameGenAt A γ) (h1 : (⟨γ, hγ.1⟩ : Ine (F := E) A) ∈ H)
    (hw : ∀ σ : Ine (F := E) A, (σ : G E Ω) ∈ Wild E A → σ ∈ H) (σ : Ine (F := E) A) : σ ∈ H := by
  have hK : IsClosed ((H.map (Ine (F := E) A).subtype : Subgroup (G E Ω)) : Set (G E Ω)) :=
    (isClosed_Ine A).isClosedEmbedding_subtypeVal.isClosedMap _ (H.isClosed_of_isOpen hH)
  have hle : Subgroup.closure (insert γ (Wild E A : Set (G E Ω))) ≤ H.map (Ine (F := E) A).subtype := by
    rw [Subgroup.closure_le]
    rintro u (rfl | hu)
    · exact ⟨⟨u, hγ.1⟩, h1, rfl⟩
    · exact ⟨⟨u, Wild_le_Ine hu⟩, hw _ hu, rfl⟩
  obtain ⟨u, hu, e⟩ := closure_minimal (SetLike.coe_subset_coe.mpr hle) hK (hγ.2 σ.2)
  rwa [← Subtype.ext (a1 := u) (a2 := σ) e]

theorem isOfFinOrder_of_isOpen {M : Type} [Group M] (φ : Ine (F := E) A →* M)
    (hφ : IsOpen (φ.ker : Set (Ine (F := E) A))) (σ : Ine (F := E) A) : IsOfFinOrder (φ σ) := by
  have : CompactSpace (Ine (F := E) A) := isCompact_iff_compactSpace.1 (isClosed_Ine A).isCompact
  have : Finite (Ine (F := E) A ⧸ φ.ker) := Subgroup.quotient_finite_of_isOpen _ hφ
  have : φ.ker.FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
  refine isOfFinOrder_iff_pow_eq_one.2 ⟨φ.ker.index, Nat.pos_of_ne_zero Subgroup.FiniteIndex.index_ne_zero, ?_⟩
  rw [← map_pow]
  exact φ.ker.pow_index_mem σ

open Classical in

theorem charpoly_eq_of_gen {n : ℕ} (ρ : Ine (F := E) A →* GL (Fin n) ℂ)
    (hρ : ∃ U : Subgroup (G E Ω), IsOpen (U : Set (G E Ω)) ∧
      ∀ σ : Ine (F := E) A, (σ : G E Ω) ∈ U → ρ σ = 1)
    {ι : Type} (s : Multiset ι) (χ : ι → G E Ω → ℂ)
    (h1 : ∀ x ∈ s, χ x 1 = 1)
    (hmul : ∀ x ∈ s, ∀ σ ∈ Ine (F := E) A, ∀ σ' ∈ Ine (F := E) A, χ x (σ * σ') = χ x σ * χ x σ')
    (hwild : ∀ x ∈ s, ∀ σ ∈ Wild E A, χ x σ = 1)
    (hopen : ∀ x ∈ s, ∃ U : Subgroup (G E Ω), IsOpen (U : Set (G E Ω)) ∧
      ∀ σ ∈ U, σ ∈ Ine (F := E) A → χ x σ = 1)
    {γ : G E Ω} (hγ : TameGenAt A γ)
    (hρw : ∀ σ : Ine (F := E) A, (σ : G E Ω) ∈ Wild E A →
      ((ρ σ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ).charpoly = (X - 1) ^ n)
    (hργ : ((ρ ⟨γ, hγ.1⟩ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ).charpoly =
      (s.map fun x => X - C (χ x γ)).prod)
    (σ : Ine (F := E) A) :
    ((ρ σ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ).charpoly = (s.map fun x => X - C (χ x σ)).prod := by
  let T := s.toFinset
  let c : T → (Ine (F := E) A →* ℂˣ) := fun x => MonoidHom.toHomUnits
    { toFun := fun σ => χ x (σ : G E Ω)
      map_one' := h1 x (Multiset.mem_toFinset.1 x.2)
      map_mul' := fun σ σ' => hmul x (Multiset.mem_toFinset.1 x.2) σ σ.2 σ' σ'.2 }
  have hc : ∀ x σ, ((c x σ : ℂˣ) : ℂ) = χ x (σ : G E Ω) := fun _ _ => rfl
  let Φ : Ine (F := E) A →* GL (Fin n) ℂ × (T → ℂˣ) := ρ.prod (Pi.monoidHom c)
  obtain ⟨U, hU, hUρ⟩ := hρ
  choose V hV hVχ using fun x : T => hopen x (Multiset.mem_toFinset.1 x.2)
  let W : Set (Ine (F := E) A) := Subtype.val ⁻¹' ((U : Set (G E Ω)) ∩ ⋂ x, (V x : Set (G E Ω)))
  have hWo : IsOpen W := continuous_subtype_val.isOpen_preimage _ (hU.inter (isOpen_iInter_of_finite hV))
  have hWk : ∀ σ ∈ W, Φ σ = 1 := by
    intro σ hσ
    refine Prod.ext (hUρ σ hσ.1) (funext fun x => Units.ext ?_)
    show χ x (σ : G E Ω) = 1
    exact hVχ x σ (Set.mem_iInter.1 hσ.2 x) σ.2
  have h1W : (1 : Ine (F := E) A) ∈ W := ⟨U.one_mem, Set.mem_iInter.2 fun x => (V x).one_mem⟩
  have hker : IsOpen (Φ.ker : Set (Ine (F := E) A)) :=
    Subgroup.isOpen_of_mem_nhds _ (g := 1)
      (Filter.mem_of_superset (hWo.mem_nhds h1W) fun σ hσ => MonoidHom.mem_ker.2 (hWk σ hσ))
  have hkerρ : IsOpen (ρ.ker : Set (Ine (F := E) A)) :=
    Subgroup.isOpen_mono (H₁ := Φ.ker) (fun σ hσ => MonoidHom.mem_ker.2 (congrArg Prod.fst (MonoidHom.mem_ker.1 hσ)))
      hker
  let γ' : Ine (F := E) A := ⟨γ, hγ.1⟩
  let H := (Subgroup.zpowers (Φ γ')).comap Φ
  have hH : IsOpen (H : Set (Ine (F := E) A)) :=
    Subgroup.isOpen_mono (H₁ := Φ.ker) (fun σ hσ => Subgroup.mem_comap.2 (by
      rw [MonoidHom.mem_ker.1 hσ]; exact one_mem _)) hker
  have hσH : σ ∈ H := by
    refine mem_of_isOpen hH hγ (Subgroup.mem_comap.2 (Subgroup.mem_zpowers _)) (fun τ hτ => ?_) σ
    refine Subgroup.mem_comap.2 ?_
    have hρ1 : ρ τ = 1 := by
      obtain ⟨m, hm, hpow⟩ := isOfFinOrder_iff_pow_eq_one.1 (isOfFinOrder_of_isOpen ρ hkerρ τ)
      exact Units.ext (GlobalTheory.FinOrd.eq_one_of_pow_eq_one_of_charpoly ℂ n _
        ⟨m, hm, by rw [← Units.val_pow_eq_pow_val, hpow, Units.val_one]⟩ (hρw τ hτ))
    have hΦ1 : Φ τ = 1 := by
      refine Prod.ext hρ1 (funext fun x => Units.ext ?_)
      show χ x (τ : G E Ω) = 1
      exact hwild x (Multiset.mem_toFinset.1 x.2) τ hτ
    rw [hΦ1]
    exact one_mem _
  obtain ⟨m, hm⟩ := ((isOfFinOrder_of_isOpen Φ hker γ').mem_powers_iff_mem_zpowers).2 (Subgroup.mem_comap.1 hσH)
  have hρm : ρ σ = ρ γ' ^ m := by
    have := congrArg Prod.fst hm
    simpa [Φ] using this.symm
  have hχm : ∀ x ∈ s, χ x γ ^ m = χ x σ := by
    intro x hx
    have := congrArg (fun p : GL (Fin n) ℂ × (T → ℂˣ) => ((p.2 ⟨x, Multiset.mem_toFinset.2 hx⟩ : ℂˣ) : ℂ)) hm
    simp only [Φ, MonoidHom.prod_apply, Prod.pow_snd, Pi.pow_apply, Units.val_pow_eq_pow_val,
      Pi.monoidHom_apply] at this
    exact this
  rw [hρm, Units.val_pow_eq_pow_val, charpoly_pow_of_prod _ s (fun x => χ x γ) hργ m]
  exact congrArg Multiset.prod (Multiset.map_congr rfl fun x hx => by rw [hχm x hx])

end Local

theorem main : ∀ D : D7, IneRep D → LabDepth D → LabGen D → ∃ Ω : TameOm D, LabIne Ω := by
  intro D hR hD hG
  obtain ⟨γ, hγ, hlab⟩ := hG
  obtain ⟨Ω, hΩ⟩ := GlobalTheory.PendOf.Model.exists_tameOm D γ hγ
  refine ⟨Ω, fun k w hw L hL => ?_⟩
  have : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
  intro σ hσ
  obtain ⟨ρ, hρ, hρP⟩ := hR k w hw L
  have hT : TameLP D L := ((hD k w hw L).2).1 hL
  have hγw := hγ.2 k w hw
  have hlabγ := hlab k w hw L hL
  have hs0 : ∀ x ∈ Formalism.CyclotomicNorms.rootsBar (D.naut.items₂ k w L), x ≠ 0 := by
    intro x hx h0
    subst h0
    have hdvd : X ∣ ((ρ ⟨γ k w, hγw.1⟩ : GL (Fin (D.naut.lpDim L)) ℂ) :
        Matrix (Fin (D.naut.lpDim L)) (Fin (D.naut.lpDim L)) ℂ).charpoly := by
      rw [← hρP ⟨γ k w, hγw.1⟩]
      rw [show ((⟨γ k w, hγw.1⟩ : ↥(Ine (F := D.host.E) (D.nd.plOm.1 w))) : GE D.nd) = γ k w from rfl, hlabγ]
      have := Multiset.dvd_prod (Multiset.mem_map_of_mem (fun x => X - C (D.ntypes.teichC k x)) hx)
      simpa [teich_zero (D.ntypes.teichC k) (D.ntypes.teichC_inj k)] using this
    rw [X_dvd_iff] at hdvd
    have hdet := Matrix.isUnits_det_units (ρ ⟨γ k w, hγw.1⟩)
    rw [Matrix.det_eq_sign_charpoly_coeff, hdvd, mul_zero] at hdet
    exact not_isUnit_zero hdet
  refine (hρP ⟨σ, hσ⟩).trans (charpoly_eq_of_gen ρ hρ _ (fun x τ => Ω.om k w x τ)
    (fun x hx => Ω.om_one k w x (hs0 x hx))
    (fun x hx => Ω.om_mul k w x (hs0 x hx))
    (fun x hx τ hτ => Ω.om_wild k w hw x (hs0 x hx) τ hτ)
    (fun x hx => Ω.om_open k w x (hs0 x hx)) hγw
    (fun τ hτ => (hρP τ).symm.trans (hT τ τ.2 hτ)) ?_ ⟨σ, hσ⟩)
  rw [← hρP ⟨γ k w, hγw.1⟩]
  refine hlabγ.trans (congrArg Multiset.prod (Multiset.map_congr rfl fun x hx => ?_))
  rw [hΩ k w hw x (hs0 x hx)]

end GlobalTheory.PendOf.LabIneAll

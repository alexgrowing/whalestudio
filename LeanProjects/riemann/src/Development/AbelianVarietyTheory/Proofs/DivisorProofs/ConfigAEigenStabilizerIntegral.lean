import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemAdelicSchwartzSpaceOfLevelCompactSchwartz
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepresentationPreservesSchwartz
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.FiniteAdeleVectorAnnihilatorsCompactOpenBasis
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsStdCharNegOneOfStandardTraceAdelicAddChar
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHaarOfIsCompact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelativelyCompactStabilizer
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsClosedAdelicLatticeClosure
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SymplecticFormBlockVanishingStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteSchrodingerLocallyTrivialStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompactUnitarySchrodingerInvarianceStatement

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.ConeSupp

theorem annih_compact : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), IsTotallyReal F → IsStd ψ →
    ∀ (κ : Type) [Fintype κ] (U : AddSubgroup (κ → FiniteAdeleRing (𝓞 F) F)), IsOpen (U : Set (κ → FiniteAdeleRing (𝓞 F) F)) →
      IsCompact {y : κ → FiniteAdeleRing (𝓞 F) F | ∀ η ∈ U, ψ (pairA F 0 (y ⬝ᵥ η)) = 1} := by
  intro F _ _ ψ hTR hψ κ _ U hUo
  classical
  haveI : IsTotallyReal F := hTR
  let e := Fintype.equivFin κ
  let g : (Fin (Fintype.card κ) → FiniteAdeleRing (𝓞 F) F) → (κ → FiniteAdeleRing (𝓞 F) F) := fun u => u ∘ e
  have hg : Continuous g := continuous_pi fun i => continuous_apply (e i)
  let gL : (Fin (Fintype.card κ) → FiniteAdeleRing (𝓞 F) F) →+ (κ → FiniteAdeleRing (𝓞 F) F) :=
    { toFun := g, map_zero' := rfl, map_add' := fun _ _ => rfl }
  have hLo : IsOpen ((U.comap gL : AddSubgroup _) : Set (Fin (Fintype.card κ) → FiniteAdeleRing (𝓞 F) F)) :=
    hUo.preimage hg
  have hA := GlobalTheory.SWQ.FinAnnih.isCompact_annihilator ψ (GlobalTheory.StdCharFromIsStd.isCharAF hψ) (fun _ => (2 : F)⁻¹)
    (fun _ => inv_ne_zero two_ne_zero) (U.comap gL) hLo
  have hBd : ∀ u v : Fin (Fintype.card κ) → FiniteAdeleRing (𝓞 F) F,
      GlobalTheory.SWQ.Bd (FiniteAdeleRing (𝓞 F) F) (fun _ => (2 : F)⁻¹) u v = g u ⬝ᵥ g v := by
    intro u v
    simp only [GlobalTheory.SWQ.Bd, mul_inv_cancel₀ (two_ne_zero' F), map_one, one_mul, dotProduct, g, Function.comp]
    exact (Equiv.sum_comp e (fun l => u l * v l)).symm
  have hge : ∀ y : κ → FiniteAdeleRing (𝓞 F) F, g (y ∘ e.symm) = y := fun y => by
    funext i; simp [g]
  convert hA.image hg using 1
  ext y
  constructor
  · intro hy
    refine ⟨y ∘ e.symm, fun v hv => ?_, hge y⟩
    rw [hBd, hge]
    exact hy _ hv
  · rintro ⟨u, hu, rfl⟩ η hη
    have hv : η ∘ e.symm ∈ U.comap gL := by
      show g (η ∘ e.symm) ∈ U
      rw [hge]; exact hη
    have := hu _ hv
    rw [hBd, hge] at this
    exact this

theorem schr_fin_inv : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), Continuous ψ →
    ∀ (κ : Type) [Fintype κ], ∀ Ψ ∈ schA F κ, ∃ N ∈ 𝓝 (0 : (κ → FiniteAdeleRing (𝓞 F) F) × (κ → FiniteAdeleRing (𝓞 F) F)),
      ∀ p ∈ N, schr ψ (fun i => pairA F 0 (p.1 i), fun i => pairA F 0 (p.2 i)) Ψ = Ψ := GlobalTheory.T.finite_schrodinger_locally_trivial

theorem symp_shift : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (b a' : ℕ) (G : Geo σ (b + 2) a') (G₁ : Geo σ b a') (H : Plane E (b + 2) b) (H' : Plane E (b + 2 + a') (b + a')),
    CfgA B G G₁ H H' → ∀ (z : Matrix (Fin b) (Fin (b + a')) (AE F E)) (l : (AE F E)ˣ),
      symp (R := AF F) (cA σ) (-1) (incM F G.V.J) (incM F G.W.J) (incM F H.ι * z * (incM F H'.ι)ᵀ) (shiftA H H' l) = 0 := GlobalTheory.T.symplectic_form_block_vanishing

theorem unif_fin : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    {n d n₁ d₁ : ℕ} (X : Spc F E n) (W : Spc F E d) (X₁ : Spc F E n₁) (W₁ : Spc F E d₁) (M : Model σ X W) (M₁ : Model σ X₁ W₁)
    (ι : Matrix (Fin n) (Fin n₁) E) (ι' : Matrix (Fin d) (Fin d₁) E) (K : Set (UA σ X.J)), IsCompact K →
    ∀ N ∈ 𝓝 (0 : (Fin n × Fin d → FiniteAdeleRing (𝓞 F) F) × (Fin n × Fin d → FiniteAdeleRing (𝓞 F) F)),
      ∃ U : AddSubgroup (Fin n₁ × Fin d₁ → FiniteAdeleRing (𝓞 F) F), IsOpen (U : Set (Fin n₁ × Fin d₁ → FiniteAdeleRing (𝓞 F) F)) ∧
        ∀ k ∈ K, ∀ η ∈ U, ∃ p ∈ N, M.co.e (mat k⁻¹ * (incM F ι * M₁.co.e.symm (0, fun i => pairA F 0 (η i)) * (incM F ι')ᵀ)) =
          (fun i => pairA F 0 (p.1 i), fun i => pairA F 0 (p.2 i)) := GlobalTheory.T.exists_open_finite_coords_mem_uniformly_on_compact

theorem schr_comm {R : Type} [CommRing R] [Invertible (2 : R)] (ψ : AddChar R ℂ) {κ : Type} [Fintype κ]
    (a c : (κ → R) × (κ → R)) (φ : (κ → R) → ℂ) (h : a.1 ⬝ᵥ c.2 = c.1 ⬝ᵥ a.2) :
    schr ψ a (schr ψ c φ) = schr ψ c (schr ψ a φ) := by
  funext x
  simp only [schr]
  rw [← mul_assoc, ← AddChar.map_add_eq_mul, ← mul_assoc, ← AddChar.map_add_eq_mul,
    show x + a.1 + c.1 = x + c.1 + a.1 by abel]
  congr 2
  simp only [add_dotProduct]
  linear_combination h

theorem dot_fe {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] (x : κ → AF F) (η : κ → FiniteAdeleRing (𝓞 F) F) :
    x ⬝ᵥ (fun i => pairA F 0 (η i)) = pairA F 0 ((fun i => (x i).2) ⬝ᵥ η) := by
  have h1 : ∀ (s : Finset κ) (f : κ → AF F), (∑ i ∈ s, f i).1 = ∑ i ∈ s, (f i).1 := fun s f =>
    map_sum (RingHom.fst (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F)) f s
  have h2 : ∀ (s : Finset κ) (f : κ → AF F), (∑ i ∈ s, f i).2 = ∑ i ∈ s, (f i).2 := fun s f =>
    map_sum (RingHom.snd (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F)) f s
  refine Prod.ext ?_ ?_
  · simp only [dotProduct, pairA]
    rw [h1]
    refine Finset.sum_eq_zero fun i _ => ?_
    change (x i).1 * (0 : InfiniteAdeleRing F) = 0
    exact mul_zero _
  · simp only [dotProduct, pairA]
    rw [h2]
    rfl

end GlobalTheory.ConeSupp

namespace GlobalTheory.ConeSupp

theorem stab_compact {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    (B : Base F E) {n : ℕ} (X : Spc F E n) (r s : ℕ) (hB : B.IsGood σ) (hX : X.IsHerm σ B r s) (K : Subgroup (UA σ X.J))
    (hK : IsStab B K) : IsCompact (K : Set (UA σ X.J)) := by
  have hKe : K = GlobalTheory.StabHaar.stabK B X := by
    ext g
    exact hK g
  obtain ⟨C, hC, hsub⟩ := GlobalTheory.StabBounded.exists_compact_superset_stabK F E σ B n X r s hB hX
  rw [hKe]
  exact hC.of_isClosed_subset (GlobalTheory.StabHaar.isClosed_stabK B X (GlobalTheory.LatHatClosed.isClosed_latHat F E n X hX.lat)) hsub

theorem supp : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (b a' : ℕ) (G : Geo σ (b + 2) a') (G₁ : Geo σ b a')
    (H : Plane E (b + 2) b) (H' : Plane E (b + 2 + a') (b + a')), CfgA B G G₁ H H' →
    ∀ e, IsEv B G.M G₁.M H.ι H'.ι (isoA H H') e → ∀ (K : Subgroup (UA σ G.V.J)), IsStab B K →
    ∀ X om om' om₁ om₁', IsTriple B G X om om' → IsTriple B G₁ X om₁ om₁' →
    ∀ Ψ ∈ schA F (Fin (b + 2) × Fin (b + 2 + a')),
      ∃ C : Set (Fin b × Fin (b + a') → FiniteAdeleRing (𝓞 F) F), IsCompact C ∧
        ∀ (k : K) (l : (AE F E)ˣ) (x : Fin b × Fin (b + a') → AF F), (fun i => (x i).2) ∉ C →
          e (G.M.co.rho B.ψ (shiftA H H' l) (om (k.1, 1) Ψ)) x = 0 := by
  intro F E _ _ _ _ _ σ B b a' G G₁ H H' hC e he K hK X om om' om₁ om₁' hT hT₁ Ψ hΨ
  have hstd : IsStd B.ψ := hT.base.std
  haveI : IsTotallyReal F := hT.base.cm.1
  have hKc : IsCompact (K : Set (UA σ G.V.J)) := stab_compact B G.V _ _ hT.base hT.geo.hV K hK
  have hsplit := (hT.weil : IsUWeilPair _ _ _ _ _ _ _ _ _ _).isUSplitting
  obtain ⟨N, hN, hNinv⟩ := schr_fin_inv F B.ψ hstd.1 _ Ψ hΨ
  obtain ⟨U, hUo, hU⟩ := unif_fin F E σ G.V G.W G₁.V G₁.W G.M G₁.M H.ι H'.ι (K : Set (UA σ G.V.J)) hKc N hN
  refine ⟨{y | ∀ η ∈ U, B.ψ (pairA F 0 (y ⬝ᵥ η)) = 1}, annih_compact F B.ψ ‹_› hstd _ U hUo, ?_⟩
  intro k l x hx
  simp only [Set.mem_setOf_eq, not_forall] at hx
  obtain ⟨η, hηU, hne⟩ := hx
  set Ω := om (k.1, 1) Ψ with hΩ
  have hΩs : Ω ∈ schA F _ := hsplit.pres _ _ hΨ
  set Φ := G.M.co.rho B.ψ (shiftA H H' l) Ω with hΦdef
  have hΦ : Φ ∈ schA F _ := GlobalTheory.HeisSchA.rho_mem_schA G.M B.ψ hstd _ _ hΩs
  set z := G₁.M.co.e.symm (0, fun i => pairA F 0 (η i)) with hz
  set w := incM F H.ι * z * (incM F H'.ι)ᵀ with hw
  obtain ⟨p, hpN, hp⟩ := hU k.1 k.2 η hηU

  have h1 : G.M.co.rho B.ψ (mat k.1⁻¹ * w) Ψ = Ψ := by
    show schr B.ψ (G.M.co.e _) Ψ = Ψ
    rw [hp]
    exact hNinv p hpN
  have h2 : G.M.co.rho B.ψ w Ω = Ω := by
    have := hsplit.impl (k.1, 1) (mat k.1⁻¹ * w) Ψ hΨ
    rw [h1] at this
    have hact : actAB (cA σ) (k.1, (1 : UA σ G.W.J)) (mat k.1⁻¹ * w) = w := by
      show mat k.1 * (mat k.1⁻¹ * w) * ((1 : GL (Fin (b + 2 + a')) (AE F E)) : Matrix _ _ (AE F E))ᵀ = w
      rw [← Matrix.mul_assoc, GlobalTheory.StabHaar.mat_mul_inv, Units.val_one, Matrix.transpose_one]
      first
        | exact (congrArg (· * (1 : Matrix (Fin (b + 2 + a')) (Fin (b + 2 + a')) (AE F E))) (Matrix.one_mul w)).trans (Matrix.mul_one w)
        | simp only [Matrix.one_mul, Matrix.mul_one]
        | simp
    rw [hact] at this
    exact this.symm
  have h3 : G.M.co.rho B.ψ w Φ = Φ := by
    rw [hΦdef]
    show schr B.ψ (G.M.co.e w) (schr B.ψ (G.M.co.e (shiftA H H' l)) Ω) = schr B.ψ (G.M.co.e (shiftA H H' l)) Ω
    rw [schr_comm]
    · exact congrArg _ h2
    · have := G.M.co.form w (shiftA H H' l)
      rw [symp_shift F E σ B b a' G G₁ H H' hC z l] at this
      linear_combination -this
  have h4 := he.Heisenberg₂ z Φ hΦ
  rw [h3] at h4
  have h5 : e Φ x = B.ψ (pairA F 0 ((fun i => (x i).2) ⬝ᵥ η)) * e Φ x := by
    conv_lhs => rw [h4]
    show schr B.ψ (G₁.M.co.e z) (e Φ) x = _
    rw [hz, LinearEquiv.apply_symm_apply]
    simp only [schr, zero_dotProduct, mul_zero, add_zero, dot_fe]
  have h6 : (1 - B.ψ (pairA F 0 ((fun i => (x i).2) ⬝ᵥ η))) * e Φ x = 0 := by
    linear_combination h5
  exact (mul_eq_zero.mp h6).resolve_left (sub_ne_zero.mpr (Ne.symm hne))

end GlobalTheory.ConeSupp

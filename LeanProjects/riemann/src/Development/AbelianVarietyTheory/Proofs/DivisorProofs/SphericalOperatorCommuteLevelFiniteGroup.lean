import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ISupIInfEigenspaceEqTop
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelHyperspecialTrivialCharacterSplitsOffPlaces
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IdemOfIsPrimeIdem

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Formalism.L2.Theta
open Formalism.IndefR Formalism.IndefR.Mult Formalism.IndefR.Lev
open scoped TensorProduct

namespace GlobalTheory.HeckeKeepsGood

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open GlobalTheory.IndefiniteRowSideFullHecke.GoodReductionModelReading

variable {D : D7}

theorem not_mem_of_offS {Sb : Finset (HeightOneSpectrum (𝓞 D.host.F))} (hSb : IsBadSet D Sb)
    {P : HeightOneSpectrum (𝓞 D.host.E)} (hP : OffS D Sb P) :
    ((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal := by
  intro h
  have h1 : P.under (𝓞 D.host.F) ∈ Sb := (hSb _).2 (by
    show algebraMap (𝓞 D.host.F) (𝓞 D.host.E) _ ∈ P.asIdeal
    rwa [map_natCast])
  obtain ⟨x, hx, hy⟩ := hP _ h1
  exact hy (algebraMap (𝓞 D.host.F) (𝓞 D.host.E) x) rfl hx

theorem mem_of_typePlace {pb : Fin 2 → 𝓞 D.host.E} {Pg : Finset (Formalism.L2.DIV.Pl D.host.E)}
    (h : IsTypePlaces D.host.g pb Pg) {PP : Formalism.L2.DIV.Pl D.host.E} (hPP : PP ∈ Pg) :
    ((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal := by
  rw [h.2, Formalism.L2.DIV.mem_primesOf] at hPP
  obtain ⟨c₀, h₀⟩ := GlobalTheory.LevSplit.exists_conj (pb 0)
  obtain ⟨c₁, h₁⟩ := GlobalTheory.LevSplit.exists_conj (pb 1)
  have e : ∀ i (c : 𝓞 D.host.E), (c : D.host.E) = star (pb i : D.host.E) → (D.host.g i : 𝓞 D.host.E) = pb i * c := by
    intro i c hc
    apply RingOfIntegers.coe_injective
    rw [map_natCast, map_mul, ← h.1.norm i, ← hc]
  rw [Nat.cast_mul, e 0 c₀ h₀, e 1 c₁ h₁, mul_mul_mul_comm]
  exact PP.asIdeal.mul_mem_right _ hPP.2

theorem sep_of_offS {Sb : Finset (HeightOneSpectrum (𝓞 D.host.F))} (hSb : IsBadSet D Sb)
    {P : HeightOneSpectrum (𝓞 D.host.E)} (hP : OffS D Sb P)
    {pb : Fin 2 → 𝓞 D.host.E} {Pg : Finset (Formalism.L2.DIV.Pl D.host.E)}
    (h : IsTypePlaces D.host.g pb Pg) {PP : Formalism.L2.DIV.Pl D.host.E} (hPP : PP ∈ Pg) :
    PP ≠ P ∧ ¬ IsConjPl PP P := by
  have h1 := not_mem_of_offS hSb hP
  have h2 := mem_of_typePlace h hPP
  refine ⟨fun e => h1 (e ▸ h2), fun hc => ?_⟩
  obtain ⟨c, hc, e⟩ := hc _ h2
  have : c = ((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 D.host.E) := by
    apply RingOfIntegers.coe_injective
    rw [map_natCast]
    refine e.trans ?_
    rw [show (((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 D.host.E) : D.host.E) = ((D.host.g 0 * D.host.g 1 : ℕ) : D.host.E) from
      map_natCast (algebraMap (𝓞 D.host.E) D.host.E) _, star_natCast]
  exact h1 (this ▸ hc)

variable {V : HSp D} {β : GL (Fin V.rank) (EAf D)} {L : Formalism.L2.DIV.LevDat D.host.E ℂ V.rank}

theorem levChi_mul {k k' : GA D V} (hk : k ∈ levG V β L) (hk' : k' ∈ levG V β L) :
    levChi V β L (k * k') = levChi V β L k * levChi V β L k' := by
  unfold levChi
  rw [← Units.val_mul, MonoidHom.map_mul]
  exact congrArg Units.val ((Formalism.L2.DIV.levChar D.sp.cm V.gram β L).map_mul ⟨_, hk.2⟩ ⟨_, hk'.2⟩)

variable {Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)} {N : ℕ}
  {Sb : Finset (HeightOneSpectrum (𝓞 D.host.F))} {P : HeightOneSpectrum (𝓞 D.host.E)} {d : List ℤ} {R : Finset (GA D V)}

theorem hasType_heckeLin (hB : IsBaseFrame V β Λ N) (hN : ((N : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal)
    (hPP : ∀ PP, PP ∈ L.Pg ∨ PP ∈ L.Q → PP ≠ P ∧ ¬ IsConjPl PP P)
    (hR : Hecke₂ V (levG V β L : Set (GA D V)) (levChi V β L) Sb P d R) {F : GA D V → ℂ}
    (hF : HasType V β L F) : HasType V β L (heckeLin V R F) :=
  GlobalTheory.SphericalOps.level_heckeLin (fun _ hk _ hk' => levChi_mul hk hk')
    (fun e f _ hI => ((GlobalTheory.LevSplit.lev_split V β Λ N L hB).2 P e f hI hN hPP).2.2) hR hF

theorem sphericalOperator_commute_levelFiniteGroup (hB : IsBaseFrame V β Λ N) (hN : ((N : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal)
    (hPP : ∀ PP, PP ∈ L.Pg ∨ PP ∈ L.Q → PP ≠ P ∧ ¬ IsConjPl PP P)
    (hR : Hecke₂ V (levG V β L : Set (GA D V)) (levChi V β L) Sb P d R) {F : GA D V → ℂ}
    (hF : HasType V β L F) (x : Formalism.L2.DIV.G0 L.Pg L.r) :
    actG0 V β L x (heckeLin V R F) = heckeLin V R (actG0 V β L x F) := by
  have hG := hasType_heckeLin hB hN hPP hR hF
  obtain ⟨e, f, ϖ, α, -, hI, -, -, -, hJ, hχ, -, -, hRs, -⟩ := hR
  unfold actG0
  split_ifs with hk
  swap
  · exact (map_zero _).symm
  have hκ := hk.choose_spec
  generalize hk.choose = κ at hκ ⊢
  obtain ⟨a1, -, a3⟩ := (GlobalTheory.LevSplit.lev_split V β Λ N (flagL L) hB).2 P e f hI hN hPP
  obtain ⟨k₁, m₁, k₂, -, s₁, s₂, rfl⟩ := a3 κ ⟨hκ.1, hκ.2.1, Subgroup.mem_top _⟩
  have m : k₁ ∈ levG V β L := (hJ k₁ s₁).2 ((a1 k₁ s₁).1 m₁)
  obtain ⟨hff, hcf, -⟩ := (GlobalTheory.T.supported_subgroup_split_commute_primeIdempotents V).2.2.1 P e f hI
  have hc : ∀ a, SuppF V f a → Commute a k₂ := fun a ha =>
    ((GlobalTheory.T.supported_subgroup_split_commute_primeIdempotents V).1 f hff hcf).2.2 (1 - f) a k₂ (by rw [mul_sub, mul_one, hff, sub_self]) ha s₂
  have key : ∀ G : GA D V → ℂ, HasType V β L G → ∀ h, G (h * (k₁ * k₂)) = G (h * k₂) := fun G hG h => by
    rw [(hc k₁ s₁).eq, ← mul_assoc, hG k₁ m, hχ k₁ m s₁, one_mul]
  funext h
  rw [key _ hG]
  show _ * ∑ γ ∈ R, F (h * k₂ * γ) = ∑ γ ∈ R, _ * F (h * γ * (k₁ * k₂))
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun γ hγ => ?_
  rw [key F hF, mul_assoc h γ, (hc γ (hRs γ hγ)).eq, mul_assoc h]

theorem heckeKeeps : ∀ D : Formalism.BasicNotions.D7, GlobalTheory.HeckeOrthSum.HeckeKeeps D := by
  intro D θ _ pb Pg hPg pl _ red ψ _ om _ Sb hSb j _ _ hj M β hβ P d R hR T hT
  obtain ⟨Λ, a, hB⟩ := hβ
  have hO : OffS D Sb P := by
    obtain ⟨_, _, _, _, h, -⟩ := hR
    exact h
  have hN : ((((D.host.g 0 * D.host.g 1) ^ a : ℕ)) : 𝓞 D.host.E) ∉ P.asIdeal := fun h =>
    not_mem_of_offS hSb hO (P.isPrime.mem_of_pow_mem a (by rwa [Nat.cast_pow] at h))
  have hPP : ∀ PP, PP ∈ (levelDatumAtBasePrime (D.sp.W j) Pg ψ).Pg ∨ PP ∈ (levelDatumAtBasePrime (D.sp.W j) Pg ψ).Q → PP ≠ P ∧ ¬ IsConjPl PP P := by
    rintro PP (h | h)
    · exact sep_of_offS hSb hO hPg h
    · exact absurd h (Finset.notMem_empty _)
  have hT1 := (GlobalTheory.MultMem.mem_mult_iff ..).1 hT.1
  refine ⟨(GlobalTheory.MultMem.mem_mult_iff ..).2 (GlobalTheory.SphericalOps.isMultMap_heckeOn hT1 (fun k hk => ?_)
    fun v => hasType_heckeLin hB hN hPP hR (hT1.lev v)), ?_⟩
  · obtain ⟨_, _, _, _, -, -, -, -, -, -, -, -, -, -, hc⟩ := hR
    exact (hc.1 k hk).1
  have hT2 : postOn M (eGoodOp (D.sp.W j) hj β ψ pl red om) T = T := sub_eq_zero.1 hT.2
  refine sub_eq_zero.2 (MultilinearMap.ext fun v => ?_)
  have h3 : eGoodOp (D.sp.W j) hj β ψ pl red om (T v) = T v := congrArg (fun U : MMap M => U v) hT2
  show eGoodOp (D.sp.W j) hj β ψ pl red om (heckeLin _ R (T v)) = heckeLin _ R (T v)
  conv_rhs => rw [← h3]
  unfold eGoodOp
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smul]
  refine Finset.sum_congr rfl fun x _ => ?_
  congr 1
  exact sphericalOperator_commute_levelFiniteGroup hB hN hPP hR (hT1.lev v) x

end GlobalTheory.HeckeKeepsGood

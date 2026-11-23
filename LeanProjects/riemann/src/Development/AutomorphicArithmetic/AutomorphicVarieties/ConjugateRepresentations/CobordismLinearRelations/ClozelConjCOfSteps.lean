import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.PartHOfSs
import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.CuspidalSupport.HasCapOneFn
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.ConjSep
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.ClozelConjCOf

noncomputable section

open NumberField IsDedekindDomain Matrix Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.GKCoh GlobalTheory.LFun
open UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible UpperTheory.V.Lit UpperTheory.V.Lit.Geo UpperTheory.V.Lit.Bor
open scoped TensorProduct

namespace UpperTheory.V.Cj

section Defs

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}

def transRep (Ξ : AlgRep E a) (q : ℕ) : Representation ℂ (GL (Fin a) (Af E)) (Co Ξ q) where
  toFun x :=
    { toFun := trans x
      map_add' := fun α β => AlternatingMap.ext fun X => map_add ((act (.fin x)).rTensor (Fin Ξ.d → ℂ)) (α X) (β X)
      map_smul' := fun c α => AlternatingMap.ext fun X => map_smul ((act (.fin x)).rTensor (Fin Ξ.d → ℂ)) c (α X) }
  map_one' := LinearMap.ext fun α => AlternatingMap.ext fun X => by
    change (finRep E a 1).rTensor (Fin Ξ.d → ℂ) (α X) = α X
    rw [map_one, Module.End.one_eq_id, LinearMap.rTensor_id]; rfl
  map_mul' x y := LinearMap.ext fun α => AlternatingMap.ext fun X => by
    change (finRep E a (x * y)).rTensor (Fin Ξ.d → ℂ) (α X) =
      (finRep E a x).rTensor (Fin Ξ.d → ℂ) ((finRep E a y).rTensor (Fin Ξ.d → ℂ) (α X))
    rw [map_mul, LinearMap.rTensor_mul]; rfl

theorem transRep_apply {Ξ : AlgRep E a} {q : ℕ} (x : GL (Fin a) (Af E)) (α : Co Ξ q) : transRep Ξ q x α = trans x α := rfl

theorem trans_one {Ξ : AlgRep E a} {q : ℕ} (α : Co Ξ q) : trans 1 α = α := by
  rw [← transRep_apply, map_one]; rfl

theorem cmp_trans {Ξ : AlgRep E a} {q : ℕ} (x : GL (Fin a) (Af E)) (α : Co Ξ q) (X : Fin q → Herm E a) (i : Fin Ξ.d) :
    cmp i (trans x α X) = finRep E a x (cmp i (α X)) := by
  change cmp i ((finRep E a x).rTensor (Fin Ξ.d → ℂ) (α X)) = _
  induction α X using TensorProduct.induction_on with
  | zero => simp
  | add y z hy hz => simp only [map_add, hy, hz]
  | tmul φ v => simp

theorem dCo_comb {Ξ : AlgRep E a} {q : ℕ} (s : ℂ) (α β : Co Ξ q) :
    dCo (smLie Ξ) (s • α + β) = s • dCo (smLie Ξ) α + dCo (smLie Ξ) β := by
  refine AlternatingMap.ext fun X => ?_
  have ap : ∀ Y, (s • α + β) Y = s • α Y + β Y := fun _ => rfl
  change _ = s • dCo (smLie Ξ) α X + dCo (smLie Ξ) β X
  simp only [dCo_apply, ap, map_add, map_smul, smul_add, Finset.sum_add_distrib, Finset.smul_sum]
  exact congrArg (· + _) (Finset.sum_congr rfl fun i _ => smul_comm _ _ _)

def Rel (σ : ℂ ≃+* ℂ) {Ξ Ξ' : AlgRep E a} (h : Ξ.d = Ξ'.d) {q : ℕ} (α : Co Ξ q) (β : Co Ξ' q) : Prop :=
  ∃ U : Subgroup (GL (Fin a) (Af E)), IsOpen (U : Set (GL (Fin a) (Af E))) ∧ IsCompact (U : Set (GL (Fin a) (Af E))) ∧
    RelAt U σ h α β

def IsPiHarm (π : CuspSub E a) (Ξ : AlgRep E a) (r : ℝ) {n : ℕ} (e : Fin n → Herm E a) {q : ℕ} (ω : Co Ξ q) : Prop :=
  Lev Ξ ω ∧ dCo (smLie Ξ) ω = 0 ∧ Coclosed (smAdj Ξ r) e ω ∧ ∀ X, ω X ∈ tens Ξ.d π.V

variable (E a) in

def ConjAt : Prop :=
  ∀ (π : CuspSub E a), (CG.mk π).IsRegAlg → ∀ σ : ℂ ≃+* ℂ,
    ∃ (π' : CuspSub E a) (τ τ' : SmIrr (GL (Fin a) (Af E))), IsFinComp π τ ∧ IsFinComp π' τ' ∧ IsConjBy σ τ τ' ∧
      ∀ (φ : E →+* ℂ) (m : Multiset ℂ), π.HasInfChar φ m → π'.HasInfChar (σ.toRingHom.comp φ) m

end Defs

def LevSub : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (Ξ : AlgRep E a) (q : ℕ),
    (∀ (U : Subgroup (GL (Fin a) (Af E))) (s : ℂ) (α β : Co Ξ q), IsLev U Ξ α → IsLev U Ξ β → IsLev U Ξ (s • α + β)) ∧
    (∀ U U' : Subgroup (GL (Fin a) (Af E)), U' ≤ U → ∀ α : Co Ξ q, (IsLev U Ξ α → IsLev U' Ξ α) ∧
      (IsRelExact U Ξ α → IsRelExact U' Ξ α)) ∧
    ∃ L : Submodule ℂ (Co Ξ q), (∀ ω, ω ∈ L ↔ Lev Ξ ω) ∧ ∀ x, ∀ ω ∈ L, trans x ω ∈ L

def CobLin : Prop :=
  ∀ (Γ M : Type) [Group Γ] [AddCommGroup M] [Module ℂ M] (ρ : Representation ℂ Γ M) (q : ℕ) (s : ℂ) (c c' : List Γ → M),
    HCob ρ q c → HCob ρ q c' → HCob ρ q (s • c + c')

def SigCob : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (U : Subgroup (GL (Fin a) (Af E))) (σ : ℂ ≃+* ℂ)
    (Ξ Ξ' : AlgRep E a) (h : Ξ.d = Ξ'.d), ConjMat σ h → ∀ (q : ℕ) c,
      HCob (levelRep ⊤ U (ratC Ξ')) q (sigC σ h c) ↔ HCob (levelRep ⊤ U (ratC Ξ)) q c

def RelPull : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (U U' : Subgroup (GL (Fin a) (Af E)))
    (x : GL (Fin a) (Af E)), (∀ u ∈ U', x⁻¹ * u * x ∈ U) → ∀ (σ : ℂ ≃+* ℂ) (Ξ Ξ' : AlgRep E a) (h : Ξ.d = Ξ'.d) (q : ℕ)
    (α : Co Ξ q) (β : Co Ξ' q), RelAt U σ h α β → RelAt U' σ h (trans x α) (trans x β)

def RelLin : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (U : Subgroup (GL (Fin a) (Af E)))
    (σ : ℂ ≃+* ℂ) (Ξ Ξ' : AlgRep E a) (h : Ξ.d = Ξ'.d) (q : ℕ) (s : ℂ) (α α' : Co Ξ q) (β β' : Co Ξ' q),
    RelAt U σ h α β → RelAt U σ h α' β' → RelAt U σ h (s • α + α') (σ s • β + β')

def RelKer : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ), 1 ≤ a → ∀ (U : Subgroup (GL (Fin a) (Af E))),
    IsCompact (U : Set (GL (Fin a) (Af E))) → ∀ (σ : ℂ ≃+* ℂ) (Ξ Ξ' : AlgRep E a) (h : Ξ.d = Ξ'.d), ConjMat σ h →
    ∀ (q : ℕ) (α : Co Ξ q) (β : Co Ξ' q), (RelAt U σ h α β → (IsRelExact U Ξ α ↔ IsRelExact U Ξ' β)) ∧
      (IsLev U Ξ α → IsLev U Ξ' β → dCo (smLie Ξ) α = 0 → dCo (smLie Ξ') β = 0 → IsRelExact U Ξ α → IsRelExact U Ξ' β →
        RelAt U σ h α β)

def RelFacts : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ), 1 ≤ a →
    ∀ (σ : ℂ ≃+* ℂ) (Ξ Ξ' : AlgRep E a) (h : Ξ.d = Ξ'.d), ConjMat σ h → ∀ q : ℕ,
    (∀ (s : ℂ) (α α' : Co Ξ q) (β β' : Co Ξ' q), Rel σ h α β → Rel σ h α' β' → Rel σ h (s • α + α') (σ s • β + β')) ∧
    (∀ x (α : Co Ξ q) (β : Co Ξ' q), Rel σ h α β → Rel σ h (trans x α) (trans x β)) ∧
    (∀ (α : Co Ξ q) (β : Co Ξ' q), Rel σ h α β → (Exact Ξ α ↔ Exact Ξ' β)) ∧
    ∀ (α : Co Ξ q) (β : Co Ξ' q), Lev Ξ α → Lev Ξ' β → dCo (smLie Ξ) α = 0 → dCo (smLie Ξ') β = 0 → Exact Ξ α → Exact Ξ' β →
      Rel σ h α β

def RelOnto : Prop :=
  PartA → ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ), 1 ≤ a →
    ∀ (σ : ℂ ≃+* ℂ) (Ξ Ξ' : AlgRep E a) (h : Ξ.d = Ξ'.d), ConjMat σ h → ∀ (q : ℕ) (M : Submodule ℂ (Co Ξ' q)),
    (∀ β ∈ M, Lev Ξ' β ∧ dCo (smLie Ξ') β = 0) →
    (∀ β : Co Ξ' q, Lev Ξ' β → dCo (smLie Ξ') β = 0 → CSupp β → ∃ β' ∈ M, Exact Ξ' (β - β')) →
    ∀ ω : Co Ξ q, Lev Ξ ω → dCo (smLie Ξ) ω = 0 → RapidD ω → ∃ β ∈ M, Rel σ h ω β

def HarmSub : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (π : CuspSub E a) (Ξ : AlgRep E a) (r : ℝ) (n : ℕ)
    (e : Fin n → Herm E a) (q : ℕ), ∃ P : Submodule ℂ (Co Ξ q), (∀ ω, ω ∈ P ↔ IsPiHarm π Ξ r e ω) ∧ ∀ x, ∀ ω ∈ P, trans x ω ∈ P

def HarmNe : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ), 1 ≤ a → ∀ (π : CuspSub E a) (Ξ : AlgRep E a) (r : ℝ)
    (n : ℕ) (e : Fin n → Herm E a), IsFrame e → HasOne Ξ r → IsCohFor π Ξ →
    ∃ (q : ℕ) (ω : Co Ξ q), ω ≠ 0 ∧ IsPiHarm π Ξ r e ω

def HarmInj : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ), 1 ≤ a → ∀ (π : CuspSub E a) (Ξ : AlgRep E a) (r : ℝ)
    (n : ℕ) (e : Fin n → Herm E a), IsFrame e → HasOne Ξ r → ∀ (q : ℕ) (ω : Co Ξ q), IsPiHarm π Ξ r e ω → Exact Ξ ω → ω = 0

def IrrAbs : Prop :=
  ∀ (G S V W ι : Type) [Group G] [AddCommGroup S] [Module ℂ S] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    [Finite ι] [Nontrivial W] (ρS : Representation ℂ G S) (ρV : Representation ℂ G V) (ρW : Representation ℂ G W),
    ρS.IsIrreducible → ⨆ f : {f : S →ₗ[ℂ] V // ∀ g v, f (ρS g v) = ρV g (f v)}, LinearMap.range f.1 = ⊤ →
    ∀ p : ι → W →ₗ[ℂ] V, (∀ i g w, p i (ρW g w) = ρV g (p i w)) → (∀ w, (∀ i, p i w = 0) → w = 0) →
      ∃ Φ : S →ₗ[ℂ] W, Function.Injective Φ ∧ ∀ g v, Φ (ρS g v) = ρW g (Φ v)

def IrrCo : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (π : CuspSub E a) (τ : SmIrr (GL (Fin a) (Af E))),
    IsFinComp π τ → ∀ (Ξ : AlgRep E a) (q : ℕ) (P : Submodule ℂ (Co Ξ q)), P ≠ ⊥ → (∀ x, ∀ ω ∈ P, trans x ω ∈ P) →
    (∀ ω ∈ P, ∀ X, ω X ∈ tens Ξ.d π.V) →
      ∃ Φ : τ.V →ₗ[ℂ] Co Ξ q, Function.Injective Φ ∧ (∀ v, Φ v ∈ P) ∧ ∀ g v, Φ (τ.ρ g v) = trans g (Φ v)

def ConjEx : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] (a : ℕ) (σ : ℂ ≃+* ℂ) (τ : SmIrr (GL (Fin a) (Af E))), ∃ τ', IsConjBy σ τ τ'

def Graph : Prop :=
  ∀ (G V V' W : Type) [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V'] [AddCommGroup W] [Module ℂ W]
    (ρ : Representation ℂ G V) (ρ' : Representation ℂ G V') (ρW : Representation ℂ G W) (σ : ℂ ≃+* ℂ) (T : V ≃+ V'),
    (∀ (c : ℂ) v, T (c • v) = σ c • T v) → (∀ g v, T (ρ g v) = ρ' g (T v)) →
    ∀ (M : Submodule ℂ W), (∀ g, ∀ w ∈ M, ρW g w ∈ M) → ∀ R : V → W → Prop,
      (∀ (s : ℂ) v v' w w', R v w → R v' w' → R (s • v + v') (σ s • w + w')) → (∀ g v w, R v w → R (ρ g v) (ρW g w)) →
      (∀ v, ∃ w ∈ M, R v w) → (∀ v, ∀ w ∈ M, R v w → (v = 0 ↔ w = 0)) →
      ∃ J : V' →ₗ[ℂ] W, Function.Injective J ∧ (∀ v, J v ∈ M) ∧ ∀ g v, J (ρ' g v) = ρW g (J v)

def Embed : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ), 1 ≤ a → ∀ (π : CuspSub E a) (σ : ℂ ≃+* ℂ)
    (Ξ Ξ' : AlgRep E a), R.IsConjRep σ Ξ Ξ' → IsCohFor π Ξ → ∀ m : (E →+* ℂ) → Multiset ℂ,
    (∀ t, AlgInfChar Ξ' t ((m t).map Neg.neg)) → ∀ τ τ' : SmIrr (GL (Fin a) (Af E)), IsFinComp π τ → IsConjBy σ τ τ' →
      ∃ j : τ'.V →ₗ[ℂ] Sm E a, j ≠ 0 ∧ (∀ g v, j (τ'.ρ g v) = finRep E a g (j v)) ∧ (∀ v, IsAutForm (j v)) ∧
        ∀ v, S.HasCap (j v) m

theorem embed_of (hH : PartH) (h1 : RelFacts) (h2 : PartA) (h3 : RelOnto) (h4 : HarmSub) (h5 : HarmNe) (h6 : HarmInj) (h7 : IrrCo)
    (h8 : Graph) (h9 : FrameEx) (h10 : OneReal) (h11 : CuspRapid) : Embed := by
  intro E _ _ _ a ha π σ Ξ Ξ' ⟨h, hσ⟩ hC m hm τ τ' hτ ⟨T, T1, T2⟩
  obtain ⟨n, e, he⟩ := h9 E a
  obtain ⟨r, hr⟩ := h10 E a Ξ
  obtain ⟨q, ω, ω0, hω⟩ := h5 E a ha π Ξ r n e he hr hC
  obtain ⟨P, P1, P2⟩ := h4 E a π Ξ r n e q
  obtain ⟨Φ, F1, F2, F3⟩ := h7 E a π τ hτ Ξ q P ((Submodule.ne_bot_iff _).2 ⟨ω, (P1 ω).2 hω, ω0⟩) P2
    fun ω hω => ((P1 ω).1 hω).2.2.2
  obtain ⟨M, M1, M2, M3, M4, M5⟩ := hH E a ha Ξ' m hm q
  obtain ⟨R1, R2, R3, R4⟩ := h1 E a ha σ Ξ Ξ' h hσ q
  have hF := fun v => (P1 _).1 (F2 v)
  have hz : ∀ Θ : AlgRep E a, Exact Θ (0 : Co Θ q) := fun Θ => by
    obtain ⟨U, u1, u2, -⟩ := hω.1
    refine ⟨U, u1, u2, ?_⟩
    cases q with
    | zero => rfl
    | succ q =>
      exact ⟨0, ⟨fun k X => by simp, fun X i _ => rfl, fun X => Submodule.zero_mem _⟩,
        AlternatingMap.ext fun X => by simp [dCo_apply]⟩
  obtain ⟨J, J1, J2, J3⟩ := h8 _ τ.V τ'.V (Co Ξ' q) τ.ρ τ'.ρ (transRep Ξ' q) σ T T1 T2 M M1 (fun v β => Rel σ h (Φ v) β)
    (fun s v v' w w' a b => by simpa only [map_add, map_smul] using R1 s _ _ _ _ a b)
    (fun g v w b => by rw [F3]; exact R2 g _ _ b)
    (fun v => h3 h2 E a ha σ Ξ Ξ' h hσ q M M2 M5 _ (hF v).1 (hF v).2.1 (h11 E a π Ξ q _ (hF v).2.2.2))
    fun v w hw b => ⟨fun e0 => M4 w hw ((R3 _ _ b).1 (by rw [e0, map_zero]; exact hz Ξ)),
      fun e0 => (map_eq_zero_iff Φ F1).1 (h6 E a ha π Ξ r n e he hr q _ (hF v) ((R3 _ _ b).2 (e0 ▸ hz Ξ')))⟩
  have : Nontrivial τ'.V := ((isIrreducible_iff τ'.ρ).1 τ'.irred).1
  obtain ⟨v, hv⟩ := exists_ne (0 : τ'.V)
  have hX : ∃ X i, cmp i (J v X) ≠ 0 := by
    by_contra hn
    push Not at hn
    refine hv ((map_eq_zero_iff J J1).1 (AlternatingMap.ext fun X => ?_))
    rw [← sum_cmp (J v X)]
    simp [hn X]
  obtain ⟨X, i, hX⟩ := hX
  refine ⟨{ toFun := fun v => cmp i (J v X)
            map_add' := fun x y => by rw [map_add, AlternatingMap.add_apply, map_add]
            map_smul' := fun c x => by rw [map_smul, AlternatingMap.smul_apply, map_smul]; rfl },
    fun e0 => hX (LinearMap.congr_fun e0 v), fun g v => ?_, fun v => (M3 _ (J2 v) X i).1,
    fun v t => ⟨by simpa using (hm t).1, (M3 _ (J2 v) X i).2 t⟩⟩
  change cmp i (J _ X) = finRep E a g (cmp i (J v X))
  rw [J3, transRep_apply, cmp_trans]

def TwReg : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a n : ℕ) (π : CG E n) (μ m : (E →+* ℂ) → Multiset ℂ),
    (∀ t, π.HasInfChar t (μ t)) → (∀ t, μ t ≤ m t) → (∀ t, R.IsRegInt a (m t)) →
    ∀ ν : HChar E, ν.IsAbsPow (((n : ℝ) - a) / 2) → (π.twist ν).IsRegAlg

def SatConj : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (n : ℕ), ConjAt E n → ∀ π : CG E n, π.IsRegAlg → ∀ σ : ℂ ≃+* ℂ,
    ∃ π' : CG E n, ∀ w B, π.HasSat w B → ∃ B', π'.HasSat w B' ∧
      algSat n (Formalism.ConjugateSelfDual.normV w) B' = (algSat n (Formalism.ConjugateSelfDual.normV w) B).map σ

def BlockConj : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a n : ℕ), ConjAt E n →
    ∀ (π : CG E n) (μ m : (E →+* ℂ) → Multiset ℂ),
    (∀ t, π.HasInfChar t (μ t)) → (∀ t, μ t ≤ m t) → (∀ t, R.IsRegInt a (m t)) → ∀ σ : ℂ ≃+* ℂ,
    ∃ π' : CG E n, ∀ w B, π.HasSat w B → ∃ B', π'.HasSat w B' ∧
      algSat a (Formalism.ConjugateSelfDual.normV w) B' = (algSat a (Formalism.ConjugateSelfDual.normV w) B).map σ

def NoEis : Prop :=
  GlobalTheory.Published.JacquetShalikaRigidity → ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ), 1 ≤ a →
    (∀ b, 1 ≤ b → b < a → ConjAt E b) → ∀ (π : CuspSub E a) (σ : ℂ ≃+* ℂ) (τ τ' : SmIrr (GL (Fin a) (Af E))),
    IsFinComp π τ → IsConjBy σ τ τ' → ∀ m : (E →+* ℂ) → Multiset ℂ, (∀ t, R.IsRegInt a (m t)) →
    ∀ (ι : Type) [Fintype ι] (n : ι → ℕ) (P : ∀ i, CG E (n i)) (μ : ι → (E →+* ℂ) → Multiset ℂ),
      2 ≤ Fintype.card ι → (∀ i, 1 ≤ n i) → (∀ i, n i < a) → (∀ i t, (P i).HasInfChar t (μ i t)) → (∀ t, ∑ i, μ i t = m t) →
      ¬ ∀ᶠ w : HeightOneSpectrum (𝓞 E) in Filter.cofinite, ∃ B : ι → Multiset ℂˣ,
        (∀ i, (P i).HasSat w (B i)) ∧ HasSatGL w (S.locOf τ'.ρ w) (∑ i, B i)

theorem clozelConjC_of_steps (hJ : GlobalTheory.Published.JacquetShalikaRigidity) (hC : Published.ClozelCohC) (hF : FinExC) (h1 : R.ExAlgRepCusp)
    (h2 : R.ConjAlgRep) (h3 : S.CuspSupport) (h4 : ConjEx) (h5 : Embed) (h6 : NoEis) : Published.ClozelConjC := by
  intro E _ _ _ a
  change 1 ≤ a → ConjAt E a
  induction a using Nat.strong_induction_on with | _ a ih => ?_
  intro ha π hπ σ
  obtain ⟨Ξ, hΞ⟩ := h1 E a π hπ
  obtain ⟨Ξ', c1, c2⟩ := h2 E a Ξ σ
  obtain ⟨τ, hτ⟩ := hF E a π
  obtain ⟨τ', hτ'⟩ := h4 E a σ τ
  have hC' := hC E a ha π Ξ hΞ
  choose m₀ m1 m2 using hΞ
  have e1 : ∀ t : E →+* ℂ, σ.toRingHom.comp (σ.symm.toRingHom.comp t) = t := fun t =>
    RingHom.ext fun x => σ.apply_symm_apply _
  have e2 : ∀ t : E →+* ℂ, σ.symm.toRingHom.comp (σ.toRingHom.comp t) = t := fun t =>
    RingHom.ext fun x => σ.symm_apply_apply _
  obtain ⟨j, j0, j1, j2, j3⟩ := h5 E a ha π σ Ξ Ξ' c1 hC' (fun t => m₀ (σ.symm.toRingHom.comp t))
    (fun t => by simpa only [e1] using c2 _ _ (m2 (σ.symm.toRingHom.comp t))) τ τ' hτ hτ'
  rcases h3 E a ha τ' _ j j0 j1 j2 j3 with ⟨π', p1, p2⟩ | ⟨ι, _, n, P, μ, k1, k2, k3, -, k4, k5, k6⟩
  · refine ⟨π', τ, τ', hτ, p1, hτ', fun φ m hm => ?_⟩
    have := p2 (σ.toRingHom.comp φ)
    rwa [e2, (m1 φ).unique hm] at this
  · refine absurd k6 (h6 hJ E a ha (fun b h hb => ih b hb h) π σ τ τ' hτ hτ' _ (fun t => ?_) ι n P μ k1 k2 k3 k4 k5)
    have h : (CG.mk π).HasInfChar _ _ := m1 (σ.symm.toRingHom.comp t)
    rw [← h.infChar_eq]
    exact ⟨CG.card_infChar _ _, hπ _⟩

end UpperTheory.V.Cj

import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.LinkedUnramifiedChains.TeichmullerParts.UnramifiedTrivialInertialType
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.LocalUnitCase.UnitaryIdeleSplitPlaceSection
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.PlaceBetween
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.CLocConjAlt
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.UnderChosenPlaceAndIsSplitAtOfDecompLe
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.PlaceEmbeddingsBijectiveInfinitePlaces
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.ExistsFixedVectorOfLocalFixedVectors
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.ExistsTensorDualEmbeddingOfHasWeightAt

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial ValuativeRel IsLocalRing Filter
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.UnitaryBC
open UpperTheory.V.W (Plc Lp HidaSetting Vl Resid LamObj)
open UpperTheory.V.HV (Coef)
open UpperTheory.V.Hi UpperTheory.V.Hi.CaseU
open UpperTheory.V.Z.Mult (Cp At IsDec CompOf Mult)
open scoped Matrix TensorProduct

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

set_option synthInstance.maxHeartbeats 200000

namespace UpperTheory.V.Z.J.D

section Comp

variable {G M : Type} [Group G] [AddCommGroup M] [Module ℂ M] {m : ℕ}
  {ρ : Representation ℂ G M} {ρF : Representation ℂ G (Fin m → M)}

private theorem fixd_pi (h : ∀ g F i, ρF g F i = ρ g (F i)) (K : Subgroup G) (F : Fin m → M) :
    F ∈ fixd ρF K ↔ ∀ i, F i ∈ fixd ρ K := by
  constructor
  · intro hF i u hu
    rw [← h, hF u hu]
  · intro hF u hu
    funext i
    rw [h, hF i u hu]

private theorem eig_pi (h : ∀ g F i, ρF g F i = ρ g (F i)) (g : G) (a : ℂ) (F : Fin m → M) :
    F ∈ Module.End.eigenspace (ρF g) a ↔ ∀ i, F i ∈ Module.End.eigenspace (ρ g) a := by
  simp only [Module.End.mem_eigenspace_iff]
  constructor
  · intro hF i
    rw [← h, hF]
    rfl
  · intro hF
    funext i
    rw [h, hF i]
    rfl

private theorem gen_pi {T : Module.End ℂ M} {T' : Module.End ℂ (Fin m → M)} (h : ∀ F i, T' F i = T (F i)) (a : ℂ)
    (F : Fin m → M) : F ∈ T'.maxGenEigenspace a ↔ ∀ i, F i ∈ T.maxGenEigenspace a := by
  have hp : ∀ (k : ℕ) (F : Fin m → M) i, ((T' - a • 1) ^ k) F i = ((T - a • 1) ^ k) (F i) := by
    intro k
    induction k with
    | zero => intro F i; rfl
    | succ k ih =>
      intro F i
      rw [pow_succ', pow_succ', Module.End.mul_apply, Module.End.mul_apply]
      simp only [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, Pi.sub_apply, Pi.smul_apply, h, ih]
  simp only [Module.End.mem_maxGenEigenspace]
  constructor
  · rintro ⟨k, hk⟩ i
    exact ⟨k, by rw [← hp, hk]; rfl⟩
  · intro hF
    choose k hk using hF
    refine ⟨Finset.univ.sup k, funext fun i => ?_⟩
    rw [hp]
    exact Module.End.pow_map_zero_of_le (Finset.le_sup (Finset.mem_univ i)) (hk i)

private theorem uOp_pi (I : Iwa G) (h : ∀ g F i, ρF g F i = ρ g (F i)) (a : G) (F : Fin m → M) (i : Fin m) :
    I.uOp ρF a F i = I.uOp ρ a (F i) := by
  haveI : Nonempty (Fin m) := ⟨i⟩
  let c : Module.End ℂ M →+ Module.End ℂ (Fin m → M) :=
    { toFun := fun T => LinearMap.compLeft T (Fin m)
      map_zero' := by ext; simp
      map_add' := fun _ _ => by ext; simp }
  have hc : Function.Injective c := fun T T' e => LinearMap.ext fun x => by
    have := congrFun (LinearMap.congr_fun e fun _ => x) i
    exact this
  have hg : ∀ g, ρF g = c (ρ g) := fun g => LinearMap.ext fun F => funext fun i => h g F i
  have : I.uOp ρF a = c (I.uOp ρ a) := by
    unfold Iwa.uOp
    rw [AddMonoidHom.map_finsum_of_injective c hc]
    exact finsum_congr fun q => hg _
  rw [this]
  rfl

private theorem eigL_pi {L : Type} [Field L] [NumberField L] {n : ℕ} {V : Type} [Fintype V] (S : V → Plc L) {W : Type}
    [AddCommGroup W] [Module ℂ W] {ρ : Representation ℂ (GV n S) W} {ρF : Representation ℂ (GV n S) (Fin m → W)}
    (h : ∀ g F i, ρF g F i = ρ g (F i)) (b : ℕ) (φ : ∀ v, Fin n → Uo ((S v).adicCompletion L) → ℂ) (μ : V → Fin n → ℂ)
    (F : Fin m → W) : F ∈ eigL S ρF b φ μ ↔ ∀ i, F i ∈ eigL S ρ b φ μ := by
  simp only [eigL, Submodule.mem_inf, Submodule.mem_iInf, fixd_pi h, eig_pi h, gen_pi (uOp_pi _ h _)]
  constructor
  · rintro ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ i
    exact ⟨⟨⟨h1 i, h2 i⟩, fun v j y => h3 v j y i⟩, fun v j => h4 v j i⟩
  · intro hF
    exact ⟨⟨⟨fun i => (hF i).1.1.1, fun i => (hF i).1.1.2⟩, fun v j y i => (hF i).1.2 v j y⟩, fun v j i => (hF i).2 v j⟩

end Comp

section Grp

variable {Ga Gp A B W : Type} [Group Ga] [Group Gp] [Group A] [Group B] [AddCommGroup W] [Module ℂ W]

private theorem lvl_iff {m : ℕ} (Ub : Subgroup Ga) (U : Subgroup Ub) (KS : Subgroup Ga) (K₁ : Subgroup A) (K₂ : Subgroup B)
    (sec : A × B →* Ga) (tk : Ub →* K₁) (τ : K₁ →* GL (Fin m) ℂ)
    (hU : ∀ g, g ∈ U.map Ub.subtype ↔ ∃ k ∈ KS, ∃ p ∈ K₁.prod K₂, g = sec p * k)
    (ht : ∀ u : Ub, ∀ k ∈ KS, ∀ p ∈ K₁.prod K₂, (u : Ga) = sec p * k → (tk u : A) = p.1)
    (F : Fin m → Ga × Gp → W) :
    (∀ u ∈ U, ∀ i g, ∑ j, (τ (tk u) : Matrix (Fin m) (Fin m) ℂ) i j • F j (g * ((u : Ga), 1)) = F i g) ↔
      (∀ k ∈ KS, ∀ i g, F i (g * (k, 1)) = F i g) ∧
      (∀ (k : K₁) i g, ∑ j, (τ k : Matrix (Fin m) (Fin m) ℂ) i j • F j (g * (sec ((k : A), 1), 1)) = F i g) ∧
      ∀ k ∈ K₂, ∀ i g, F i (g * (sec (1, k), 1)) = F i g := by
  have hsub : ∀ p ∈ K₁.prod K₂, ∃ u ∈ U, (u : Ga) = sec p := fun p hp => by
    obtain ⟨u, hu, e⟩ := (hU (sec p)).2 ⟨1, one_mem _, p, hp, (mul_one _).symm⟩
    exact ⟨u, hu, e⟩
  constructor
  · intro hF
    have h1 : ∀ u ∈ U, (tk u : A) = 1 → ∀ i g, F i (g * ((u : Ga), 1)) = F i g := fun u hu e i g => by
      have e' : tk u = 1 := Subtype.ext e
      have := hF u hu i g
      rw [e', map_one] at this
      simpa [Matrix.one_apply] using this
    refine ⟨fun k hk i g => ?_, fun k i g => ?_, fun k hk i g => ?_⟩
    · obtain ⟨u, hu, e⟩ := (hU k).2 ⟨k, hk, 1, one_mem _, by simp⟩
      have e' : (u : Ga) = k := e
      rw [← e']
      exact h1 u hu (ht u k hk 1 (one_mem _) (by simp [e'])) i g
    · have hp : ((k : A), (1 : B)) ∈ K₁.prod K₂ := ⟨k.2, one_mem _⟩
      obtain ⟨u, hu, e⟩ := hsub _ hp
      have e' : tk u = k := Subtype.ext (ht u 1 (one_mem _) _ hp (by rw [e, mul_one]))
      have := hF u hu i g
      rwa [e', e] at this
    · have hp : ((1 : A), k) ∈ K₁.prod K₂ := ⟨one_mem _, hk⟩
      obtain ⟨u, hu, e⟩ := hsub _ hp
      rw [← e]
      exact h1 u hu (ht u 1 (one_mem _) _ hp (by rw [e, mul_one])) i g
  · rintro ⟨a, b, c⟩ u hu i g
    obtain ⟨k, hk, p, hp, e⟩ := (hU u).1 ⟨u, hu, rfl⟩
    have e1 : tk u = ⟨p.1, hp.1⟩ := Subtype.ext (ht u k hk p hp e)
    have e2 : sec p = sec (1, p.2) * sec (p.1, 1) := by
      rw [← map_mul]
      congr 1
      exact Prod.ext (by simp) (by simp)
    have e3 : ∀ j, F j (g * ((u : Ga), 1)) = F j ((g * (sec (1, p.2), 1)) * (sec (p.1, 1), 1)) := fun j => by
      have : g * ((u : Ga), (1 : Gp)) = ((g * (sec (1, p.2), 1)) * (sec (p.1, 1), 1)) * (k, 1) := by
        rw [e, e2]
        exact Prod.ext (by simp [mul_assoc]) (by simp)
      rw [this, a k hk]
    simp only [e3, e1]
    rw [b ⟨p.1, hp.1⟩ i (g * (sec (1, p.2), 1))]
    exact c _ hp.2 i g

end Grp

section U

variable {l : ℕ} [Fact l.Prime] {L Ω : Type} [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω]

variable (n : ℕ) (s : HidaSetting l L Ω) in

private def kS : Subgroup (UA L n) :=
  GlobalTheory.UnitaryBC.finU L n ⊓ (⨅ (u : Plc L) (_ : u.under (𝓞 (Lp L)) ∉ s.S), (KO (u.adicCompletion L) (Fin n)).comap (cLoc u)) ⊓
    ⨅ (v : Plc (Lp L)) (_ : v ∈ s.S), (cLoc (s.w v)).ker

private theorem mem_kS {n : ℕ} {s : HidaSetting l L Ω} {k : UA L n} : k ∈ kS n s ↔ k ∈ GlobalTheory.UnitaryBC.finU L n ∧
    (∀ u : Plc L, u.under (𝓞 (Lp L)) ∉ s.S → cLoc u k ∈ KO (u.adicCompletion L) (Fin n)) ∧
    ∀ v ∈ s.S, cLoc (s.w v) k = 1 := by
  simp only [kS, Subgroup.mem_inf, Subgroup.mem_iInf, Subgroup.mem_comap, MonoidHom.mem_ker, and_assoc]

private theorem local_retraction_cases {n : ℕ} (w u : Plc L) (x : UA L n) :
    cLoc u (GlobalTheory.DefU.LocRet.ret0 w n x) = cLoc u x ∨ cLoc u (GlobalTheory.DefU.LocRet.ret0 w n x) = 1 := by
  by_cases h : u.under (𝓞 (Lp L)) = w.under (𝓞 (Lp L))
  · exact Or.inl (GlobalTheory.DefU.LocRet.localProj_unitaryAdelicLocalRetractionEnd_of_under_eq h x)
  · exact Or.inr (GlobalTheory.DefU.LocRet.localProj_unitaryAdelicLocalRetractionEnd_of_under_ne h x)

private theorem retraction_mem_level {n : ℕ} {s : HidaSetting l L Ω} (w : Plc L) {k : UA L n} (hk : k ∈ kS n s) :
    GlobalTheory.DefU.LocRet.ret0 w n k ∈ kS n s := by
  obtain ⟨-, h2, h3⟩ := mem_kS.1 hk
  refine mem_kS.2 ⟨(Subgroup.mem_inf.1 (GlobalTheory.DefU.LocRet.unitaryAdelicLocalRetractionEnd_mem_localPoints k)).1, fun u hu => ?_, fun v hv => ?_⟩
  · rcases local_retraction_cases w u k with h | h <;> rw [h]
    · exact h2 u hu
    · exact one_mem _
  · exact (local_retraction_cases w _ k).elim (fun h => h.trans (h3 v hv)) id

private theorem kS_vec {n : ℕ} {s : HidaSetting l L Ω} (V : s.Lev) (hV : V.S' = s.S) {σ : Submodule ℂ (UA L n → ℂ)} (hσ : IsAutRepU σ)
    (hun : ∀ w : Plc L, w.under (𝓞 (Lp L)) ∉ s.S → IsUnramU σ w) :
    ∃ φ ∈ σ, φ ≠ 0 ∧ ∀ k ∈ kS n s, RU L n k φ = φ := by
  obtain ⟨hund, hspl⟩ := UpperTheory.under_chosen_place_and_isSplitAt_of_decomp_le l L Ω s
  have hsplit : ∀ w : Plc L, w.under (𝓞 (Lp L)) ∈ s.S → IsSplitAt w := fun w hw => hspl w (V.split _ (hV ▸ hw))
  have hKO : ∀ u : Plc L, KO (u.adicCompletion L) (Fin n) = GlobalTheory.LFun.KGL u n :=
    fun u => GlobalTheory.SmGL.SphCompletion.KO_completion u n
  have hT : ((fun w : Plc L => w.under (𝓞 (Lp L))) ⁻¹' s.S).Finite := by
    refine (hV ▸ V.fin : s.S.Finite).preimage' fun v _ => ?_
    have := v.isMaximal
    refine ((IsDedekindDomain.primesOver_finite v.asIdeal (𝓞 L)).preimage
      (f := fun w : Plc L => w.asIdeal) (fun a _ b _ h => HeightOneSpectrum.ext h)).subset ?_
    rintro w rfl
    exact ⟨w.isPrime, ⟨rfl⟩⟩
  refine UpperTheory.exists_fixed_vector_of_local_fixed_vectors L n σ hσ (kS n s) (fun k hk => (mem_kS.1 hk).1) (fun w k hk => retraction_mem_level w hk) _ hT
    (fun k hk u hu => hKO u ▸ (mem_kS.1 hk).2.1 u hu) fun w => ?_
  by_cases hw : w.under (𝓞 (Lp L)) ∈ s.S
  · obtain ⟨φ, hφ, h0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hσ.ne_bot
    refine ⟨φ, hφ, h0, fun k hk hl => ?_⟩
    have hu : (s.w (w.under (𝓞 (Lp L)))).under (𝓞 (Lp L)) = w.under (𝓞 (Lp L)) := hund _
    have hl' : k ∈ locU n (s.w (w.under (𝓞 (Lp L)))) := by
      unfold locU at hl ⊢
      rw [hu]
      exact hl
    have h2 : k = 1 := congrArg Subtype.val
      (GlobalTheory.SplitPts.eq_one_of_cLoc (hsplit _ (hu.symm ▸ hw)) ⟨k, hl'⟩ ((mem_kS.1 hk).2.2 _ hw))
    rw [h2, map_one]
    rfl
  · obtain ⟨φ, h1, h2, h3⟩ := hun w hw
    exact ⟨φ, h1, h2, fun k hk hl => h3 k hl (hKO w ▸ (mem_kS.1 hk).2.1 w hw)⟩

private theorem toGS_cmp {n : ℕ} {s : HidaSetting l L Ω} {k : Ga l L n} (hk : toGS n s k = 1) :
    (∀ u : s.St, cmp n (s.w u) k = 1) ∧ cmp n (s.w s.v0) k = 1 :=
  ⟨fun u => congrFun (congrArg Prod.fst hk) u, congrArg Prod.snd hk⟩

private theorem KS_lift {n : ℕ} {s : HidaSetting l L Ω} (V : s.Lev) {k : Ga l L n} (hk : k ∈ KS n s) {x : UA L n}
    (hx : x ∈ GlobalTheory.UnitaryBC.finU L n) (h1 : (away l L n).rangeRestrict x = k)
    (h2 : ∀ v : V.frame.Vl, cLoc (s.w v.1) x = 1) : x ∈ kS n s := by
  obtain ⟨hk1, hk2⟩ := Subgroup.mem_inf.1 hk
  obtain ⟨c1, c2⟩ := toGS_cmp (MonoidHom.mem_ker.1 hk1)
  have hw := (UpperTheory.under_chosen_place_and_isSplitAt_of_decomp_le l L Ω s).1
  have hc : ∀ v : Plc L, ((l : ℕ) : 𝓞 (Lp L)) ∉ (v.under (𝓞 (Lp L))).asIdeal → cLoc v x = cmp n v k := fun v hv => by
    rw [← h1, UpperTheory.V.Hi.Pu.cmp_of (fun h => hv ((UpperTheory.V.Hi.Pu.l_iff v).2 h))]
  refine mem_kS.2 ⟨hx, fun u hu => ?_, fun v hv => ?_⟩
  · rw [hc u fun h => hu (Or.inl h)]
    exact Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 hk2 u) hu
  · by_cases h : ((l : ℕ) : 𝓞 (Lp L)) ∈ v.asIdeal
    · exact h2 ⟨v, h⟩
    · rw [hc _ (by rwa [hw])]
      rcases hv with h' | h' | h'
      · exact absurd h' h
      · exact c1 ⟨v, h'⟩
      · rw [h']
        exact c2

variable {n : ℕ} {s : HidaSetting l L Ω} {V : s.Lev} {lam : Wt L l n} {d : ℕ}

private def tl (ι : Qbar l ≃+* ℂ) (e : (Fin d → ℂ) ≃ₗ[ℂ] ⨂[ℂ] e : Emb l (fun v : V.frame.Vl => s.w v.1), nablaSq ℂ n (lam e.res))
    (ℓ : Module.Dual ℂ (⨂[ℂ] e : Emb l (fun v : V.frame.Vl => s.w v.1), nablaSq ℂ n (lam e.res))) :
    (Ga l L n × GV n (fun v : V.frame.Vl => s.w v.1) → Fin d → ℂ) →ₗ[ℂ] (UA L n → ℂ) where
  toFun F := toForm ι e F ℓ
  map_add' F F' := funext fun g => by simp [toForm]
  map_smul' a F := funext fun g => by simp [toForm]

private theorem vs_ne (hn : 1 ≤ n) (hV : V.S' = s.S) (Q : QData V) {c : Coef l} (ι : Qbar l ≃+* ℂ) {m : ℕ}
    (τ₀ : KT n (wt s) →* GL (Fin m) c.O)
    (e : (Fin d → ℂ) ≃ₗ[ℂ] ⨂[ℂ] e : Emb l (fun v : V.frame.Vl => s.w v.1), nablaSq ℂ n (lam e.res))
    (ξ : GV n (fun v : V.frame.Vl => s.w v.1) →* GL (Fin d) ℂ) (hb : IsBasis ι e ξ) {σ : Submodule ℂ (UA L n → ℂ)} (hσ : IsAutRepU σ)
    (hun : ∀ w : Plc L, w.under (𝓞 (Lp L)) ∉ s.S → IsUnramU σ w)
    (hwt : ∀ y : Emb l (fun v : V.frame.Vl => s.w v.1), HasWeightAt σ (ι.toRingHom.comp y.res) (lam y.res).dual) :
    VS V ι e ξ Q τ₀ σ ≠ ⊥ := by
  obtain ⟨φ, hφ, hφ0, hφK⟩ := kS_vec (n := n) V hV hσ hun
  obtain ⟨hfin, hbij⟩ := UpperTheory.placeEmbeddings_bijective_infinitePlaces l L Ω s V ι
  have hcomm : ∀ x ∈ infU L n, ∀ k ∈ GlobalTheory.UnitaryBC.finU L n, ∀ ψ, RU L n k (RU L n x ψ) = RU L n x (RU L n k ψ) :=
    fun x hx k hk ψ => by rw [GlobalTheory.DefU.RU_RU, GlobalTheory.DefU.RU_RU, GlobalTheory.DefU.fin_mul_inf hk hx]
  let M : Submodule ℂ (UA L n → ℂ) := σ ⊓ fixd (RU L n) (kS n s)
  let N : Submodule ℂ (Fin 1 → UA L n → ℂ) := M.comap (LinearMap.proj 0)
  have hN0 : N ≠ ⊥ := (Submodule.ne_bot_iff _).2 ⟨fun _ => φ, ⟨hφ, hφK⟩, fun h => hφ0 (congrFun h 0)⟩
  have hNσ : ∀ F ∈ N, ∀ k, F k ∈ σ := fun F hF k => by
    rw [Subsingleton.elim k 0]
    exact hF.1
  have hNs : ∀ x ∈ infU L n, ∀ F ∈ N, (fun k => RU L n x (F k)) ∈ N := fun x hx F hF =>
    ⟨hσ.stable _ _ hF.1, fun k hk => by
      have h2 : RU L n k (F 0) = F 0 := hF.2 k hk
      change RU L n k (RU L n x (F 0)) = RU L n x (F 0)
      rw [hcomm x hx k (mem_kS.1 hk).1, h2]⟩
  obtain ⟨Φ, hΦ0, hΦN, hΦ⟩ := UpperTheory.exists_tensor_dual_embedding_of_hasWeightAt L n hn _ _ hbij (fun x => lam x.res) σ hσ hwt 1 N hN0 hNσ hNs
  obtain ⟨f1, -, -, f4, f5⟩ := formU l L Ω s n hn V Q c m τ₀ ι lam d e ξ hb _ fun _ => rfl
  let A : Submodule ℂ (Ga l L n × GV n (fun v : V.frame.Vl => s.w v.1) → Fin d → ℂ) := (hset Q τ₀).X.AF ξ
  obtain ⟨F, hFA, hF'⟩ : ∃ F : Ga l L n × GV n (fun v : V.frame.Vl => s.w v.1) → Fin d → ℂ, F ∈ A ∧ ∀ ℓ, toForm ι e F ℓ = Φ ℓ 0 :=
    f5 ((LinearMap.proj 0 : (Fin 1 → UA L n → ℂ) →ₗ[ℂ] (UA L n → ℂ)) ∘ₗ Φ)
      (fun ℓ => hσ.aut _ (hΦN ℓ).1) fun ℓ x hx => hΦ ℓ x hx 0
  refine (Submodule.ne_bot_iff _).2 ⟨F, ⟨⟨hFA, Submodule.subset_span fun ℓ => ?_⟩, fun k hk => ?_⟩, fun h => hΦ0 ?_⟩
  · rw [hF']
    exact (hΦN ℓ).1
  · obtain ⟨x, hx⟩ := f4 (k, 1)
    have hx1 : (away l L n).rangeRestrict (x : UA L n) = k := congrArg Prod.fst hx
    have hx2 : ∀ v : V.frame.Vl, cLoc (s.w v.1) (x : UA L n) = 1 := congrFun (congrArg Prod.snd hx)
    have hxK := KS_lift V hk x.2 hx1 hx2
    have hJ : UpperTheory.V.Hi.Pu.JU V (x : UA L n) = (k, 1) := hx
    have hmem : (fun g => F (g * (k, 1))) ∈ A := UpperTheory.V.Hi.Pu.AF_tr _ hFA _
    refine sub_eq_zero.1 (f1 _ (A.sub_mem hmem hFA) fun ℓ => ?_)
    have e3 := UpperTheory.V.Hi.Pu.RU_fin ι e F ℓ x.2
    rw [hJ, hF'] at e3
    have e4 : toForm ι e (fun g => F (g * (k, 1))) ℓ = Φ ℓ 0 := e3.symm.trans ((hΦN ℓ).2 _ hxK)
    have e5 : tl ι e ℓ ((fun g => F (g * (k, 1))) - F) = 0 := by
      rw [map_sub]
      change toForm ι e (fun g => F (g * (k, 1))) ℓ - toForm ι e F ℓ = 0
      rw [e4, hF', sub_self]
    exact e5
  · refine LinearMap.ext fun ℓ => funext fun i => ?_
    rw [Subsingleton.elim i 0, ← hF', h]
    exact (tl ι e ℓ).map_zero

end U

section U2

private theorem fix_iff {Γ Ga Gp : Type} [Group Γ] [Group Ga] [Group Gp] (X : Frame Γ Ga Gp) {d m : ℕ}
    (τ : X.Ub →* GL (Fin m) ℂ) (U : Subgroup X.Ub) (F : Fin m → X.Fn ℂ d) :
    F ∈ fixd (X.raF d τ) U ↔
      ∀ u ∈ U, ∀ i g, ∑ j, (τ u : Matrix (Fin m) (Fin m) ℂ) i j • F j (g * ((u : Ga), 1)) = F i g := by
  constructor
  · intro h u hu i g
    have h1 := congrFun (h u hu) i
    rw [UpperTheory.V.Hi.Pu.raF_eq] at h1
    have h2 := congrFun h1 g
    simpa only [Finset.sum_apply, Pi.smul_apply] using h2
  · intro h u hu
    funext i
    rw [UpperTheory.V.Hi.Pu.raF_eq]
    funext g
    simpa only [Finset.sum_apply, Pi.smul_apply] using h u hu i g

private theorem sum_fun {X W : Type} [AddCommGroup W] [Module ℂ W] {m : ℕ} (c : Fin m → ℂ) (f : Fin m → X → W) (h : X → W) :
    ∑ j, c j • f j = h ↔ ∀ g, ∑ j, c j • f j g = h g := by
  constructor
  · intro e g
    simpa only [Finset.sum_apply, Pi.smul_apply] using congrFun e g
  · intro e
    funext g
    simpa only [Finset.sum_apply, Pi.smul_apply] using e g

variable {l : ℕ} [Fact l.Prime] {L Ω : Type} [Field L] [NumberField L] [IsCMField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω]
  {n : ℕ} {s : HidaSetting l L Ω}

private theorem toGS_sec (hb : Function.Bijective ((toGS n s).comp (GaS n s).subtype)) (p : GS n s) :
    toGS n s (secS n s p) = p := by
  unfold secS
  rw [dif_pos hb]
  exact (MulEquiv.ofBijective _ hb).apply_symm_apply p

private theorem toKT_eq (hb : Function.Bijective ((toGS n s).comp (GaS n s).subtype)) (u : Ub n s) {k : Ga l L n} (hk : k ∈ KS n s)
    {p : GS n s} (e : (u : Ga l L n) = secS n s p * k) : (toKT n s u : GV n (wt s)) = p.1 := by
  obtain ⟨c1, -⟩ := toGS_cmp (MonoidHom.mem_ker.1 (Subgroup.mem_inf.1 hk).1)
  funext a
  have h1 : cmp n (s.w a) (secS n s p) = p.1 a := congrFun (congrArg Prod.fst (toGS_sec hb p)) a
  change cmp n (s.w a) (u : Ga l L n) = _
  rw [e, map_mul, c1, mul_one, h1]

variable {V : s.Lev} {lam : Wt L l n} {d : ℕ}

private theorem y_iff (hS : SecS) (hn : 1 ≤ n) (hV : V.S' = s.S) (Q : QData V) {c : Coef l} (ι : Qbar l ≃+* ℂ) {m : ℕ}
    (τ₀ : KT n (wt s) →* GL (Fin m) c.O)
    (e : (Fin d → ℂ) ≃ₗ[ℂ] ⨂[ℂ] e : Emb l (fun v : V.frame.Vl => s.w v.1), nablaSq ℂ n (lam e.res))
    (ξ : GV n (fun v : V.frame.Vl => s.w v.1) →* GL (Fin d) ℂ) (σ : Submodule ℂ (UA L n → ℂ))
    (F : Fin m → Ga l L n × GV n (fun v : V.frame.Vl => s.w v.1) → Fin d → ℂ) :
    F ∈ YOf Q ι τ₀ e ξ σ ↔
      F ∈ invT (KT n (wt s)) (Kc _ n 1) ((Matrix.GeneralLinearGroup.map (ι.toRingHom.comp (algebraMap c.O (Qbar l)))).comp τ₀)
        ((actS n V d).comp (MonoidHom.inr _ _)) ∧ ∀ i, F i ∈ VS V ι e ξ Q τ₀ σ := by
  obtain ⟨hb, -, h3⟩ := hS l L Ω s n hn V hV
  have lvl := lvl_iff (Gp := GV n (fun v : V.frame.Vl => s.w v.1)) (Ub n s) (UQ n Q) (KS n s) (KT n (wt s)) (Kc _ n 1) (secS n s) (toKT n s)
    ((Matrix.GeneralLinearGroup.map (ι.toRingHom.comp (algebraMap c.O (Qbar l)))).comp τ₀) (h3 Q)
    (fun u k hk p _ e => toKT_eq hb u hk e) F
  refine (UpperTheory.V.Hi.Pu.mem_Y Q τ₀ ι e).trans ?_
  constructor
  · rintro ⟨⟨hA, hfix⟩, hσ'⟩
    obtain ⟨a, b, c'⟩ := lvl.1 ((fix_iff _ _ _ F).1 hfix)
    exact ⟨⟨fun k i => (sum_fun _ _ _).2 (b k i), fun k hk i => funext (c' k hk i)⟩, fun i =>
      ⟨⟨hA i trivial, Submodule.subset_span fun ℓ => hσ' i ℓ⟩, fun k hk => funext (a k hk i)⟩⟩
  · rintro ⟨⟨b1, b2⟩, hv⟩
    refine ⟨⟨fun i _ => (hv i).1.1, (fix_iff _ _ _ F).2 (lvl.2 ⟨fun k hk i g => congrFun ((hv i).2 k hk) g,
      fun k i => (sum_fun _ _ _).1 (b1 k i), fun k hk i g => congrFun (b2 k hk i) g⟩)⟩, fun i ℓ => ?_⟩
    have h' : Submodule.span ℂ {F' : Ga l L n × GV n (fun v : V.frame.Vl => s.w v.1) → Fin d → ℂ | ∀ ℓ, toForm ι e F' ℓ ∈ σ} ≤
        σ.comap (tl ι e ℓ) := Submodule.span_le.2 fun F' hF' => hF' ℓ
    exact h' (hv i).1.2

private theorem part_eq (hS : SecS) (hn : 1 ≤ n) (hV : V.S' = s.S) (Q : QData V) {c : Coef l} (ι : Qbar l ≃+* ℂ) {m : ℕ}
    (τ₀ : KT n (wt s) →* GL (Fin m) c.O)
    (e : (Fin d → ℂ) ≃ₗ[ℂ] ⨂[ℂ] e : Emb l (fun v : V.frame.Vl => s.w v.1), nablaSq ℂ n (lam e.res))
    (ξ : GV n (fun v : V.frame.Vl => s.w v.1) →* GL (Fin d) ℂ) (σ : Submodule ℂ (UA L n → ℂ))
    (R : Submodule ℂ (Ga l L n × GV n (fun v : V.frame.Vl => s.w v.1) → Fin d → ℂ)) (hR : R = VS V ι e ξ Q τ₀ σ) (b : ℕ)
    (φ : ∀ v : V.frame.Vl, Fin n → Uo ((s.w v.1).adicCompletion L) → ℂ) (μ : V.frame.Vl → Fin n → ℂ) :
    YOf Q ι τ₀ e ξ σ ⊓ eigL (fun v : V.frame.Vl => s.w v.1) ((hset Q τ₀).X.rpF ℂ d m) b φ μ =
      invT (KT n (wt s)) (Kc _ n 1) ((Matrix.GeneralLinearGroup.map (ι.toRingHom.comp (algebraMap c.O (Qbar l)))).comp τ₀)
        ((actS n V d).comp (MonoidHom.inr _ _)) ⊓ Submodule.pi Set.univ fun _ =>
        R ⊓ eigL (fun v : V.frame.Vl => s.w v.1) ((actS n V d).comp (MonoidHom.inl _ _)) b φ μ := by
  have hrp : ∀ (g : GV n (fun v : V.frame.Vl => s.w v.1)) (F : Fin m → Ga l L n × GV n (fun v : V.frame.Vl => s.w v.1) → Fin d → ℂ) i,
      (hset Q τ₀).X.rpF ℂ d m g F i = (actS n V d).comp (MonoidHom.inl _ _) g (F i) := fun g F i => by
    have h1 : (secS n s) 1 = 1 := map_one _
    change rtr ℂ _ _ (1, g) (F i) = rtr ℂ _ _ (secS n s 1, g) (F i)
    rw [h1]
  subst hR
  ext F
  have h1 := y_iff hS hn hV Q ι τ₀ e ξ σ F
  have h2 := eigL_pi (fun v : V.frame.Vl => s.w v.1) hrp b φ μ F
  constructor
  · rintro ⟨y, z⟩
    obtain ⟨y1, y2⟩ := h1.1 y
    exact ⟨y1, fun i _ => ⟨y2 i, h2.1 z i⟩⟩
  · rintro ⟨y, z⟩
    exact ⟨h1.2 ⟨y, fun i => (z i trivial).1⟩, h2.2 fun i => (z i trivial).2⟩

private theorem rank_of {M : Type} [AddCommGroup M] [Module ℂ M] {A B : Submodule ℂ M} (h : A = B) {r : Cardinal}
    (hB : Module.rank ℂ B = r) : Module.rank ℂ A = r := h ▸ hB

end U2

end UpperTheory.V.Z.J.D

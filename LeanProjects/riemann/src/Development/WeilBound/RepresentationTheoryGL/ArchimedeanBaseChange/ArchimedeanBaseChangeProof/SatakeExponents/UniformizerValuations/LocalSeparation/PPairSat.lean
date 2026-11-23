import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.ReadMod

noncomputable section

open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.BCT GlobalTheory.LFun Formalism.L2.Host
open PositivityTheory.Rg.Rs PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation PositivityTheory.Rg.BcB.G8

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.Rg.BcB.F.RS

section Gen

variable {G₁ G₂ V : Type} [Group G₁] [Group G₂] [AddCommGroup V] [Module ℂ V]

theorem heckeVec_pairProd (ρ : Representation ℂ (G₁ × G₂) V) {K₁ : Subgroup G₁} {K₂ : Subgroup G₂}
    (hK₁ : IsCommensurated K₁) (hK₂ : IsCommensurated K₂) {h₁ : G₁ → ℂ} {h₂ : G₂ → ℂ}
    (hh₁ : h₁ ∈ Hecke ℂ K₁) (hh₂ : h₂ ∈ Hecke ℂ K₂) {x : V} (hx : x ∈ fixed ρ (K₁.prod K₂)) :
    heckeVec ρ (K₁.prod K₂) (fun g => h₁ g.1 * h₂ g.2) x =
      heckeVec (ρ.comp (MonoidHom.inl G₁ G₂)) K₁ h₁ (heckeVec (ρ.comp (MonoidHom.inr G₁ G₂)) K₂ h₂ x) := by
  classical
  let e : (G₁ × G₂) ⧸ K₁.prod K₂ ≃ (G₁ ⧸ K₁) × (G₂ ⧸ K₂) :=
    { toFun := fun c => ((c.out.1 : G₁ ⧸ K₁), (c.out.2 : G₂ ⧸ K₂))
      invFun := fun p => (((p.1.out, p.2.out) : G₁ × G₂) : (G₁ × G₂) ⧸ K₁.prod K₂)
      left_inv := fun c => by
        conv_rhs => rw [← c.out_eq']
        exact QuotientGroup.eq.2 (Subgroup.mem_prod.2
          ⟨QuotientGroup.eq.1 (QuotientGroup.out_eq' _), QuotientGroup.eq.1 (QuotientGroup.out_eq' _)⟩)
      right_inv := fun p => by
        obtain ⟨k, hk⟩ := QuotientGroup.mk_out_eq_mul (K₁.prod K₂) ((p.1.out, p.2.out) : G₁ × G₂)
        simp only [hk, Prod.fst_mul, Prod.snd_mul]
        rw [QuotientGroup.mk_mul_of_mem _ (Subgroup.mem_prod.1 k.2).1,
          QuotientGroup.mk_mul_of_mem _ (Subgroup.mem_prod.1 k.2).2, QuotientGroup.out_eq', QuotientGroup.out_eq'] }
  have hbi : IsBiInv (K₁.prod K₂) (fun g : G₁ × G₂ => h₁ g.1 * h₂ g.2) := fun a b g => by
    have e1 := hh₁.1 ⟨_, (Subgroup.mem_prod.1 a.2).1⟩ ⟨_, (Subgroup.mem_prod.1 b.2).1⟩ g.1
    have e2 := hh₂.1 ⟨_, (Subgroup.mem_prod.1 a.2).2⟩ ⟨_, (Subgroup.mem_prod.1 b.2).2⟩ g.2
    exact congrArg₂ (· * ·) e1 e2
  have hf1 := Formalism.UG.P.finite_support_cosets hK₁ hh₁.2
  have hf2 := Formalism.UG.P.finite_support_cosets hK₂ hh₂.2
  let F : (G₁ ⧸ K₁) × (G₂ ⧸ K₂) → V := fun p => (h₁ p.1.out * h₂ p.2.out) • ρ (p.1.out, p.2.out) x
  have hF : Function.HasFiniteSupport F := by
    refine (hf1.prod hf2).subset fun p hp => ⟨fun h0 => hp ?_, fun h0 => hp ?_⟩
    · simp [F, h0]
    · simp [F, h0]
  rw [heckeVec_eq_of_section hbi hx (fun c => ((e c).1.out, (e c).2.out)) (fun c => e.left_inv c)]
  rw [show (∑ᶠ c, (fun g : G₁ × G₂ => h₁ g.1 * h₂ g.2) ((e c).1.out, (e c).2.out) •
      ρ ((e c).1.out, (e c).2.out) x) = ∑ᶠ c, F (e c) from rfl, finsum_comp_equiv e, finsum_curry F hF]
  simp only [heckeVec]
  refine finsum_congr fun c₁ => ?_
  have hm := ((h₁ c₁.out • (ρ.comp (MonoidHom.inl G₁ G₂)) c₁.out : V →ₗ[ℂ] V).toAddMonoidHom.map_finsum
    (finite_heckeVec hK₂ hh₂ (ρ.comp (MonoidHom.inr G₁ G₂)) x))
  simp only [LinearMap.toAddMonoidHom_coe, LinearMap.smul_apply] at hm
  rw [hm]
  refine finsum_congr fun c₂ => ?_
  simp only [F, MonoidHom.coe_comp, Function.comp_apply, MonoidHom.inl_apply, MonoidHom.inr_apply, map_smul, smul_smul]
  rw [← Module.End.mul_apply, ← map_mul, Prod.mk_mul_mk, mul_one, one_mul]

theorem heckeVec_smul_pair (ρ : Representation ℂ G₁ V) {K : Subgroup G₁} (hK : IsCommensurated K) {h : G₁ → ℂ}
    (hh : h ∈ Hecke ℂ K) (c : ℂ) (x : V) : heckeVec ρ K h (c • x) = c • heckeVec ρ K h x := by
  have := map_heckeVec (ρ := ρ) hK hh (c • LinearMap.id) (ρ' := ρ) (fun g y => by simp) x
  simpa using this.symm

theorem heckeVec_zero_pair (ρ : Representation ℂ G₁ V) (K : Subgroup G₁) (h : G₁ → ℂ) : heckeVec ρ K h 0 = 0 := by
  simp [heckeVec]

end Gen

section Pair

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {a b : ℕ}

theorem pairSlice₁ {U₁ : Submodule ℂ (Sm E a)} {U₂ : Submodule ℂ (Sm E b)} {G : H E a b → ℂ}
    (hG : G ∈ pairSpace U₁ U₂) (y : GA E b) : ∃ φ ∈ U₁, ∀ x, φ.1 x = G (x, y) := by
  induction hG using Submodule.span_induction with
  | mem F hF =>
    obtain ⟨φ₁, h₁, φ₂, h₂, rfl⟩ := hF
    exact ⟨φ₂.1 y • φ₁, U₁.smul_mem _ h₁, fun x => by simp [mul_comm]⟩
  | zero => exact ⟨0, U₁.zero_mem, fun x => rfl⟩
  | add F F' _ _ hF hF' =>
    obtain ⟨φ, hφ, e⟩ := hF
    obtain ⟨φ', hφ', e'⟩ := hF'
    exact ⟨φ + φ', U₁.add_mem hφ hφ', fun x => by simp [e, e']⟩
  | smul c F _ hF =>
    obtain ⟨φ, hφ, e⟩ := hF
    exact ⟨c • φ, U₁.smul_mem c hφ, fun x => by simp [e]⟩

theorem pairSlice₂ {U₁ : Submodule ℂ (Sm E a)} {U₂ : Submodule ℂ (Sm E b)} {G : H E a b → ℂ}
    (hG : G ∈ pairSpace U₁ U₂) (x : GA E a) : ∃ φ ∈ U₂, ∀ y, φ.1 y = G (x, y) := by
  induction hG using Submodule.span_induction with
  | mem F hF =>
    obtain ⟨φ₁, h₁, φ₂, h₂, rfl⟩ := hF
    exact ⟨φ₁.1 x • φ₂, U₂.smul_mem _ h₂, fun y => by simp⟩
  | zero => exact ⟨0, U₂.zero_mem, fun y => rfl⟩
  | add F F' _ _ hF hF' =>
    obtain ⟨φ, hφ, e⟩ := hF
    obtain ⟨φ', hφ', e'⟩ := hF'
    exact ⟨φ + φ', U₂.add_mem hφ hφ', fun y => by simp [e, e']⟩
  | smul c F _ hF =>
    obtain ⟨φ, hφ, e⟩ := hF
    exact ⟨c • φ, U₂.smul_mem c hφ, fun y => by simp [e]⟩

def pairSatEvA (y : GA E b) : (H E a b → ℂ) →ₗ[ℂ] (GA E a → ℂ) := LinearMap.funLeft ℂ ℂ fun x : GA E a => ((x, y) : H E a b)

def pairSatEvB (x : GA E a) : (H E a b → ℂ) →ₗ[ℂ] (GA E b → ℂ) := LinearMap.funLeft ℂ ℂ fun y : GA E b => ((x, y) : H E a b)

theorem pairSatEvA_equiv (w : Pl E) (y : GA E b) (g : GLw a w) (F : H E a b → ℂ) :
    pairSatEvA y (((pairRt a b w).comp (MonoidHom.inl _ _)) g F) =
      ((rightReg ℂ (GA E a) ℂ).comp (embW a w)) g (pairSatEvA y F) := by
  funext x
  show F ((x, y) * (embW a w g, embW b w 1)) = F (x * embW a w g, y)
  rw [map_one, Prod.mk_mul_mk, mul_one]

theorem pairSatEvB_equiv (w : Pl E) (x : GA E a) (g : GLw b w) (F : H E a b → ℂ) :
    pairSatEvB x (((pairRt a b w).comp (MonoidHom.inr _ _)) g F) =
      ((rightReg ℂ (GA E b) ℂ).comp (embW b w)) g (pairSatEvB x F) := by
  funext y
  show F ((x, y) * (embW a w 1, embW b w g)) = F (x, y * embW b w g)
  rw [map_one, Prod.mk_mul_mk, mul_one]

end Pair

theorem pairSat_holds : PairSat := by
  intro hT E _ _ _ a b s₁ s₂ Pa Pb w G g₁ g₂ u₁ u₂ t₁ t₂ hG h0 hf
  obtain ⟨⟨x₀, y₀⟩, hp⟩ : ∃ p, G p ≠ 0 := by
    by_contra hc
    push Not at hc
    exact h0 (funext hc)
  have fixA : ∀ y (φ : Sm E a), (∀ x, φ.1 x = G (x, y)) → ∀ k ∈ KGL w a, finRep E a (locGL E a w k) φ = φ := by
    intro y φ e k hk
    refine Subtype.ext (funext fun x => ?_)
    show φ.1 (x * finGL E a (locGL E a w k)) = φ.1 x
    have := congrFun (GlobalTheory.LGrp.mem_fixed.1 hf (k, 1) (Subgroup.mem_prod.2 ⟨hk, one_mem _⟩)) (x, y)
    change G ((x, y) * (embW a w k, embW b w 1)) = G (x, y) at this
    rw [map_one, Prod.mk_mul_mk, mul_one] at this
    rw [e, e]
    exact this
  have fixB : ∀ x (φ : Sm E b), (∀ y, φ.1 y = G (x, y)) → ∀ k ∈ KGL w b, finRep E b (locGL E b w k) φ = φ := by
    intro x φ e k hk
    refine Subtype.ext (funext fun y => ?_)
    show φ.1 (y * finGL E b (locGL E b w k)) = φ.1 y
    have := congrFun (GlobalTheory.LGrp.mem_fixed.1 hf (1, k) (Subgroup.mem_prod.2 ⟨one_mem _, hk⟩)) (x, y)
    change G ((x, y) * (embW a w 1, embW b w k)) = G (x, y) at this
    rw [map_one, Prod.mk_mul_mk, mul_one] at this
    rw [e, e]
    exact this
  obtain ⟨φa, hφa, ea⟩ := pairSlice₁ hG y₀
  obtain ⟨φb, hφb, eb⟩ := pairSlice₂ hG x₀
  have na : φa ≠ 0 := fun h => hp (by rw [← ea x₀, h]; rfl)
  have nb : φb ≠ 0 := fun h => hp (by rw [← eb y₀, h]; rfl)
  obtain ⟨Ba, sa, hBa⟩ := hT E a s₁ Pa w g₁ u₁ t₁ ⟨φa, hφa, na, fixA y₀ φa ea⟩
  obtain ⟨Bb, sb, hBb⟩ := hT E b s₂ Pb w g₂ u₂ t₂ ⟨φb, hφb, nb, fixB x₀ φb eb⟩
  have eigA : ∀ ϖ, IsUnifV E w ϖ → ∀ i ≤ a, heckeVec ((pairRt a b w).comp (MonoidHom.inl _ _)) (KGL w a)
      (Tj ℂ a (Ov E w) ϖ i) G = satEig (qV E w) a Ba i • G := by
    intro ϖ hϖ i hi
    funext ⟨x, y⟩
    obtain ⟨φ, hφ, e⟩ := pairSlice₁ hG y
    have key := congrFun (map_heckeVec (Final.GLintComm E w a) (Tj_mem_hecke hϖ i) (pairSatEvA y)
      (ρ := (pairRt a b w).comp (MonoidHom.inl _ _)) (ρ' := (rightReg ℂ (GA E a) ℂ).comp (embW a w))
      (pairSatEvA_equiv w y) G) x
    have hev : pairSatEvA y G = φ.1 := funext fun x => (e x).symm
    rw [hev] at key
    change heckeVec ((pairRt a b w).comp (MonoidHom.inl _ _)) (KGL w a) (Tj ℂ a (Ov E w) ϖ i) G (x, y) = _ at key
    rw [key, Pi.smul_apply, ← e x]
    by_cases hz : φ = 0
    · subst hz
      simp [heckeVec_zero_pair]
    · have hs := (hBa φ hφ hz (fixA y φ e)).map (Sm E a).subtype
        (ρ' := (rightReg ℂ (GA E a) ℂ).comp (embW a w)) (fun g z => rfl) (by simpa using hz)
      have he : heckeVec ((rightReg ℂ (GA E a) ℂ).comp (embW a w)) (KGL w a) (Tj ℂ a (Ov E w) ϖ i) φ.1 =
          satEig (qV E w) a Ba i • φ.1 := hs.2.2.2 ϖ hϖ i hi
      rw [he]
      rfl
  have eigB : ∀ ϖ, IsUnifV E w ϖ → ∀ j ≤ b, heckeVec ((pairRt a b w).comp (MonoidHom.inr _ _)) (KGL w b)
      (Tj ℂ b (Ov E w) ϖ j) G = satEig (qV E w) b Bb j • G := by
    intro ϖ hϖ j hj
    funext ⟨x, y⟩
    obtain ⟨φ, hφ, e⟩ := pairSlice₂ hG x
    have key := congrFun (map_heckeVec (Final.GLintComm E w b) (Tj_mem_hecke hϖ j) (pairSatEvB x)
      (ρ := (pairRt a b w).comp (MonoidHom.inr _ _)) (ρ' := (rightReg ℂ (GA E b) ℂ).comp (embW b w))
      (pairSatEvB_equiv w x) G) y
    have hev : pairSatEvB x G = φ.1 := funext fun y => (e y).symm
    rw [hev] at key
    change heckeVec ((pairRt a b w).comp (MonoidHom.inr _ _)) (KGL w b) (Tj ℂ b (Ov E w) ϖ j) G (x, y) = _ at key
    rw [key, Pi.smul_apply, ← e y]
    by_cases hz : φ = 0
    · subst hz
      simp [heckeVec_zero_pair]
    · have hs := (hBb φ hφ hz (fixB x φ e)).map (Sm E b).subtype
        (ρ' := (rightReg ℂ (GA E b) ℂ).comp (embW b w)) (fun g z => rfl) (by simpa using hz)
      have he : heckeVec ((rightReg ℂ (GA E b) ℂ).comp (embW b w)) (KGL w b) (Tj ℂ b (Ov E w) ϖ j) φ.1 =
          satEig (qV E w) b Bb j • φ.1 := hs.2.2.2 ϖ hϖ j hj
      rw [he]
      rfl
  refine ⟨Ba, Bb, sa, sb, hf, (hBa φa hφa na (fixA y₀ φa ea)).2.2.1, (hBb φb hφb nb (fixB x₀ φb eb)).2.2.1,
    fun ϖ hϖ i hi j hj => ?_⟩
  rw [heckeVec_pairProd _ (Final.GLintComm E w a) (Final.GLintComm E w b) (Tj_mem_hecke hϖ i) (Tj_mem_hecke hϖ j) hf,
    eigB ϖ hϖ j hj, heckeVec_smul_pair _ (Final.GLintComm E w a) (Tj_mem_hecke hϖ i), eigA ϖ hϖ i hi, smul_smul,
    mul_comm]

end PositivityTheory.Rg.BcB.F.RS

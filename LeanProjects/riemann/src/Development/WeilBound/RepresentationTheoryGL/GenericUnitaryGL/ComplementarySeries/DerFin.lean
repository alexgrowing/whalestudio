import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.ComplementarySeries.Complementary
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LeviIrreducibleTensorDecomposition
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsSmoothIterPhi
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HighestDerivativeOfProduct
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ParabolicProductHasFiniteLengthGL
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsIrreducibleSubquotientTwoBlockConstituents
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InductionFiniteLength
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCuspProdCharTransport
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.BernsteinZelevinskyFiniteness
import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.WhittakerCuspidal.WhitCuspOfSegCuspGeneric

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.SplitWeil GlobalTheory.BZMir
open scoped TensorProduct

namespace PositivityTheory.RgGu.NR.DerFin

section Gen

variable {G M V W X : Type} [Group G] [Group M] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
  [AddCommGroup X] [Module ℂ X] (N : Subgroup G) (θ : N →* ℂˣ) (s : M →* G)
  (hs : ∀ (m : M) (n : N), ∃ h : s m * (n : G) * (s m)⁻¹ ∈ N, θ ⟨_, h⟩ = θ n)

def dMap {ρ : Representation ℂ G V} {σ : Representation ℂ G W} (f : ρ.IntertwiningMap σ) :
    (twAct ρ N θ s hs).IntertwiningMap (twAct σ N θ s hs) :=
  ⟨twMap ρ σ N θ f.toLinearMap (fun g v => Representation.IntertwiningMap.isIntertwining _ _ f g v), fun m =>
    Submodule.linearMap_qext _ (LinearMap.ext fun v => by
      show Submodule.Quotient.mk (f (ρ (s m) v)) = Submodule.Quotient.mk (σ (s m) (f v))
      rw [Representation.IntertwiningMap.isIntertwining])⟩

theorem dMap_mk {ρ : Representation ℂ G V} {σ : Representation ℂ G W} (f : ρ.IntertwiningMap σ) (v : V) :
    dMap N θ s hs f (Submodule.Quotient.mk v) = Submodule.Quotient.mk (f v) := rfl

theorem dMap_surjective {ρ : Representation ℂ G V} {σ : Representation ℂ G W} (f : ρ.IntertwiningMap σ)
    (hf : Function.Surjective f) : Function.Surjective (dMap N θ s hs f) := by
  intro x
  induction x using Submodule.Quotient.induction_on with
  | H w =>
    obtain ⟨v, rfl⟩ := hf w
    exact ⟨Submodule.Quotient.mk v, rfl⟩

theorem twKer_le_map {ρ : Representation ℂ G V} {σ : Representation ℂ G W} (p : ρ.IntertwiningMap σ)
    (hp : Function.Surjective p) : twKer σ N θ ≤ (twKer ρ N θ).map p.toLinearMap := by
  refine Submodule.span_le.2 ?_
  rintro w ⟨n, y, rfl⟩
  obtain ⟨v, rfl⟩ := hp y
  refine ⟨ρ (n : G) v - (θ n : ℂ) • v, Submodule.subset_span ⟨n, v, rfl⟩, ?_⟩
  show p (ρ (n : G) v - (θ n : ℂ) • v) = σ (n : G) (p v) - (θ n : ℂ) • p v
  rw [map_sub, map_smul, Representation.IntertwiningMap.isIntertwining]

theorem d_exact {ρ₁ : Representation ℂ G V} {ρ₂ : Representation ℂ G W} {ρ₃ : Representation ℂ G X}
    (ι : ρ₁.IntertwiningMap ρ₂) (p : ρ₂.IntertwiningMap ρ₃) (hp : Function.Surjective p)
    (hex : ∀ v, p v = 0 → ∃ u, ι u = v) :
    ∀ x, dMap N θ s hs p x = 0 → ∃ y, dMap N θ s hs ι y = x := by
  intro x hx
  induction x using Submodule.Quotient.induction_on with
  | H v =>
    rw [dMap_mk, Submodule.Quotient.mk_eq_zero] at hx
    obtain ⟨w, hw, hpw⟩ := twKer_le_map N θ p hp hx
    obtain ⟨u, hu⟩ := hex (v - w) (by rw [map_sub]; exact sub_eq_zero.2 hpw.symm)
    refine ⟨Submodule.Quotient.mk u, ?_⟩
    rw [dMap_mk, hu, Submodule.Quotient.mk_sub, (Submodule.Quotient.mk_eq_zero _).2 hw, sub_zero]

omit [Group M] in
theorem subsingleton_tw {ρ : Representation ℂ G V} [Subsingleton V] : Subsingleton (TwJacquet ρ N θ) :=
  ⟨fun x y => by
    induction x using Submodule.Quotient.induction_on with
    | H a =>
      induction y using Submodule.Quotient.induction_on with
      | H b => rw [Subsingleton.elim a b]⟩

def topBot (ρ : Representation ℂ G V) : (subQuot (⊤ : Subrepresentation ρ) ⊥).IntertwiningMap ρ :=
  ⟨Submodule.liftQ _ (⊤ : Subrepresentation ρ).toSubmodule.subtype (fun x hx => by
      rw [LinearMap.mem_ker]
      exact (Submodule.mem_bot ℂ).1 hx), fun g => Submodule.linearMap_qext _ (LinearMap.ext fun x => rfl)⟩

theorem topBot_surjective (ρ : Representation ℂ G V) : Function.Surjective (topBot ρ) :=
  fun v => ⟨Submodule.Quotient.mk ⟨v, trivial⟩, rfl⟩

end Gen

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

section Base

variable (ψ : AddChar k Circle) {n t : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]

def phi (n t : ℕ) : Levi k (fun a : Fin 2 => Fin (![n, t] a)) →* GL (Fin n) k × GL (Fin t) k :=
  (Pi.evalMonoidHom (fun a : Fin 2 => GL (Fin (![n, t] a)) k) 0).prod
    (Pi.evalMonoidHom (fun a : Fin 2 => GL (Fin (![n, t] a)) k) 1)

def lift2 {n t : ℕ} (g : GL (Fin n) k) (h : GL (Fin t) k) : Levi k (fun a : Fin 2 => Fin (![n, t] a)) :=
  fun a => match a with
    | ⟨0, _⟩ => g
    | ⟨1, _⟩ => h
    | ⟨i + 2, hi⟩ => absurd hi (by omega)

theorem phi_lift2 {n t : ℕ} (g : GL (Fin n) k) (h : GL (Fin t) k) : phi n t (lift2 g h) = (g, h) := rfl

theorem phi_surjective (n t : ℕ) : Function.Surjective (phi (k := k) n t) := by
  rintro ⟨g, h⟩
  exact ⟨lift2 g h, phi_lift2 g h⟩

theorem phi_continuous (n t : ℕ) : Continuous (phi (k := k) n t) :=
  (continuous_apply 0).prodMk (continuous_apply 1)

theorem base (hc : Continuous ψ) (h1 : ψ ≠ 1) (Y : Representation ℂ (GL (Fin n) k × GL (Fin t) k) V)
    (hYs : IsSmooth Y) (hYi : Y.IsIrreducible) :
    HasFiniteLength (twAct Y (rightUnip k n t) (rightWhit k ψ n t) (MonoidHom.inl _ _) (inl_stab ψ n t)) := by
  classical
  let τ : IrrRep (Levi k fun a : Fin 2 => Fin (![n, t] a)) :=
    ⟨V, Y.comp (phi n t), isSmooth_comp hYs _ (phi_continuous n t),
      GlobalTheory.FinGL.Transport.isIrreducible_comp Y _ (phi_surjective n t) hYi⟩
  obtain ⟨σ, ⟨E⟩⟩ := GlobalTheory.CompanionTheory.LeviTensor.nonempty_equiv_piTensor GlobalTheory.CompanionTheory.BZCuspPair.irrAdm ![n, t] τ
  let A := (σ 0).rep.V
  let B := (σ 1).rep.V
  let α : Representation ℂ (GL (Fin n) k) A := (σ 0).rep.ρ
  let β : Representation ℂ (GL (Fin t) k) B := (σ 1).rep.ρ
  let Ψ : V ≃ₗ[ℂ] A ⊗[ℂ] B :=
    E.toLinearEquiv.trans (GlobalTheory.CompanionTheory.HighestDeriv.piFinTwoTensor fun a => (σ a).rep.V)

  have hP : ∀ f : ∀ a : Fin 2, (σ a).rep.V,
      GlobalTheory.CompanionTheory.HighestDeriv.piFinTwoTensor (fun a => (σ a).rep.V) (PiTensorProduct.tprod ℂ f) = f 0 ⊗ₜ f 1 := by
    intro f
    rw [← LinearEquiv.eq_symm_apply]
    show PiTensorProduct.tprod ℂ f = GlobalTheory.SmGL.MultiIrr.tensorCons _ ((LinearEquiv.lTensor _
      (PiTensorProduct.subsingletonEquiv (s := fun i : Fin 1 => (σ i.succ).rep.V) 0).symm) (f 0 ⊗ₜ f 1))
    have e1 : (PiTensorProduct.subsingletonEquiv (s := fun i : Fin 1 => (σ i.succ).rep.V) 0).symm (f 1) =
        PiTensorProduct.tprod ℂ (fun i : Fin 1 => f i.succ) := by
      rw [LinearEquiv.symm_apply_eq, PiTensorProduct.subsingletonEquiv_apply_tprod]
      rfl
    rw [LinearEquiv.lTensor_tmul, e1, GlobalTheory.SmGL.MultiIrr.tensorCons_tmul]
    congr 1
    exact (Fin.cons_self_tail f).symm

  have hΨ : ∀ (g : GL (Fin n) k) (h : GL (Fin t) k) (v : V),
      Ψ (Y (g, h) v) = TensorProduct.map (α g) (β h) (Ψ v) := by
    intro g h v
    obtain ⟨l, hl⟩ := phi_surjective (k := k) n t (g, h)
    have e1 : E (Y (g, h) v) = piTensor (fun a => (σ a).rep.ρ) l (E v) := by
      rw [← hl]
      exact Representation.IntertwiningMap.isIntertwining _ _ E.toIntertwiningMap l v
    have hl0 : l 0 = g := congrArg Prod.fst hl
    have hl1 : l 1 = h := congrArg Prod.snd hl
    show GlobalTheory.CompanionTheory.HighestDeriv.piFinTwoTensor _ (E (Y (g, h) v)) = _
    rw [e1]
    show _ = TensorProduct.map (α g) (β h) (GlobalTheory.CompanionTheory.HighestDeriv.piFinTwoTensor _ (E v))
    induction E v using PiTensorProduct.induction_on with
    | smul_tprod c f =>
      simp only [map_smul, piTensor_tprod, hP, TensorProduct.map_tmul, ← hl0, ← hl1]
      rfl
    | add x y hx hy => rw [map_add, map_add, map_add, hx, hy, map_add]
  set K : Submodule ℂ B := twKer β (unipB k (Fin t)) (whitChar ψ t) with hK

  have hgen : ∀ (a : A) (b : B), b ∈ K → Ψ.symm (a ⊗ₜ b) ∈ twKer Y (rightUnip k n t) (rightWhit k ψ n t) := by
    intro a b hb
    induction hb using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨u, y, rfl⟩ := hx
      have hu : ((1 : GL (Fin n) k), (u : GL (Fin t) k)) ∈ rightUnip k n t :=
        Subgroup.mem_prod.2 ⟨Subgroup.one_mem _, u.2⟩
      refine Submodule.subset_span ⟨⟨_, hu⟩, Ψ.symm (a ⊗ₜ y), ?_⟩
      apply Ψ.injective
      rw [LinearEquiv.apply_symm_apply, map_sub, map_smul, hΨ, LinearEquiv.apply_symm_apply,
        TensorProduct.map_tmul, TensorProduct.tmul_sub, TensorProduct.tmul_smul, map_one, Module.End.one_apply]
      rfl
    | zero => rw [TensorProduct.tmul_zero, map_zero]; exact Submodule.zero_mem _
    | add x y _ _ hx hy => rw [TensorProduct.tmul_add, map_add]; exact Submodule.add_mem _ hx hy
    | smul c x _ hx => rw [TensorProduct.tmul_smul, map_smul]; exact Submodule.smul_mem _ c hx
  have hrange : ∀ z ∈ LinearMap.range (K.subtype.lTensor A),
      Ψ.symm z ∈ twKer Y (rightUnip k n t) (rightWhit k ψ n t) := by
    rintro _ ⟨z, rfl⟩
    induction z using TensorProduct.induction_on with
    | zero => rw [map_zero, map_zero]; exact Submodule.zero_mem _
    | tmul a b => rw [LinearMap.lTensor_tmul]; exact hgen a b b.2
    | add x y hx hy => rw [map_add, map_add]; exact Submodule.add_mem _ hx hy

  have hrk : Module.rank ℂ (B ⧸ K) ≤ 1 :=
    PositivityTheory.rg.gu.whit.whitRankIrr k ψ hc h1 t B β (σ 1).rep.smooth (σ 1).rep.irr
  by_cases htop : K = ⊤
  ·
    have hall : ∀ v : V, v ∈ twKer Y (rightUnip k n t) (rightWhit k ψ n t) := by
      intro v
      have hs : Function.Surjective (K.subtype.lTensor A) := by
        apply LinearMap.lTensor_surjective
        intro b
        exact ⟨⟨b, htop ▸ Submodule.mem_top⟩, rfl⟩
      obtain ⟨z, hz⟩ := hs (Ψ v)
      have := hrange (Ψ v) ⟨z, hz⟩
      rwa [LinearEquiv.symm_apply_apply] at this
    haveI : Subsingleton (TwJacquet Y (rightUnip k n t) (rightWhit k ψ n t)) :=
      ⟨fun x y => by
        induction x using Submodule.Quotient.induction_on with
        | H a =>
          induction y using Submodule.Quotient.induction_on with
          | H b =>
            rw [(Submodule.Quotient.mk_eq_zero _).2 (hall a), (Submodule.Quotient.mk_eq_zero _).2 (hall b)]⟩
    exact GlobalTheory.ProdLength.hasFiniteLength_of_subsingleton _
  ·
    have hnt : Nontrivial (B ⧸ K) := Submodule.Quotient.nontrivial_iff.2 htop
    have hfr : Module.finrank ℂ (B ⧸ K) = 1 := by
      have hfin : Module.rank ℂ (B ⧸ K) < Cardinal.aleph0 := lt_of_le_of_lt hrk Cardinal.one_lt_aleph0
      haveI : Module.Finite ℂ (B ⧸ K) := Module.rank_lt_aleph0_iff.1 hfin
      have h2 : (Module.finrank ℂ (B ⧸ K) : Cardinal) ≤ 1 := by rw [Module.finrank_eq_rank]; exact hrk
      have h3 : 0 < Module.finrank ℂ (B ⧸ K) := Module.finrank_pos
      have h4 : Module.finrank ℂ (B ⧸ K) ≤ 1 := by exact_mod_cast h2
      omega
    haveI : Module.Finite ℂ (B ⧸ K) := Module.finite_of_finrank_eq_succ hfr
    let q : (B ⧸ K) ≃ₗ[ℂ] ℂ := LinearEquiv.ofFinrankEq _ _ (by simp [hfr])
    let ℓ : B →ₗ[ℂ] ℂ := q.toLinearMap ∘ₗ K.mkQ
    have hℓs : Function.Surjective ℓ := q.surjective.comp (Submodule.mkQ_surjective K)
    have hex : Function.Exact K.subtype ℓ := by
      intro b
      constructor
      · intro hb
        have : K.mkQ b = 0 := q.injective (by rw [map_zero]; exact hb)
        exact ⟨⟨b, (Submodule.Quotient.mk_eq_zero K).1 this⟩, rfl⟩
      · rintro ⟨b', rfl⟩
        show q (Submodule.Quotient.mk (b' : B)) = 0
        rw [(Submodule.Quotient.mk_eq_zero K).2 b'.2, map_zero]
    have hexA := lTensor_exact A hex hℓs
    let e' : A ⊗[ℂ] B →ₗ[ℂ] A := (TensorProduct.rid ℂ A).toLinearMap ∘ₗ ℓ.lTensor A
    have he'_tmul : ∀ (a : A) (b : B), e' (a ⊗ₜ b) = ℓ b • a := fun a b => by
      show (TensorProduct.rid ℂ A) (a ⊗ₜ ℓ b) = ℓ b • a
      rw [TensorProduct.rid_tmul]
    have hℓK : ∀ b ∈ K, ℓ b = 0 := fun b hb => by
      show q (Submodule.Quotient.mk b) = 0
      rw [(Submodule.Quotient.mk_eq_zero K).2 hb, map_zero]

    have hker : twKer Y (rightUnip k n t) (rightWhit k ψ n t) ≤ LinearMap.ker (e' ∘ₗ Ψ.toLinearMap) := by
      refine Submodule.span_le.2 ?_
      rintro w ⟨⟨⟨a, u⟩, hu⟩, v, rfl⟩
      have ha : a = 1 := Subgroup.mem_bot.1 (Subgroup.mem_prod.1 hu).1
      subst ha
      have hu2 : u ∈ unipB k (Fin t) := (Subgroup.mem_prod.1 hu).2
      show e' (Ψ (Y (1, u) v - _)) = 0
      rw [map_sub, map_smul, hΨ, map_sub, map_smul, sub_eq_zero]
      induction Ψ v using TensorProduct.induction_on with
      | zero => simp
      | tmul x y =>
        rw [TensorProduct.map_tmul, he'_tmul, he'_tmul, map_one, Module.End.one_apply, smul_smul]
        congr 1
        have hm : β u y - (whitChar ψ t ⟨u, hu2⟩ : ℂ) • y ∈ K := Submodule.subset_span ⟨⟨u, hu2⟩, y, rfl⟩
        have := hℓK _ hm
        rw [map_sub, map_smul, sub_eq_zero] at this
        rw [this, smul_eq_mul]
        rfl
      | add x y hx hy => simp only [map_add, smul_add, hx, hy]

    let F : TwJacquet Y (rightUnip k n t) (rightWhit k ψ n t) →ₗ[ℂ] A :=
      (twKer Y (rightUnip k n t) (rightWhit k ψ n t)).liftQ (e' ∘ₗ Ψ.toLinearMap) hker
    have hFmk : ∀ v, F (Submodule.Quotient.mk v) = e' (Ψ v) := fun v => rfl
    have hFinj : Function.Injective F := by
      rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
      intro x hx
      induction x using Submodule.Quotient.induction_on with
      | H v =>
        rw [LinearMap.mem_ker, hFmk] at hx
        have h0 : ℓ.lTensor A (Ψ v) = 0 := by
          have h' : (TensorProduct.rid ℂ A) (ℓ.lTensor A (Ψ v)) = 0 := hx
          exact (TensorProduct.rid ℂ A).map_eq_zero_iff.1 h'
        obtain ⟨z, hz⟩ := (hexA (Ψ v)).1 h0
        have := hrange (Ψ v) ⟨z, hz⟩
        rw [LinearEquiv.symm_apply_apply] at this
        exact (Submodule.Quotient.mk_eq_zero _).2 this
    let Fi : (twAct Y (rightUnip k n t) (rightWhit k ψ n t) (MonoidHom.inl _ _) (inl_stab ψ n t)).IntertwiningMap α :=
      ⟨F, fun g => Submodule.linearMap_qext _ (LinearMap.ext fun v => by
        show F (Submodule.Quotient.mk (Y (g, 1) v)) = α g (F (Submodule.Quotient.mk v))
        rw [hFmk, hFmk, hΨ]
        induction Ψ v using TensorProduct.induction_on with
        | zero => simp
        | tmul x y => rw [TensorProduct.map_tmul, he'_tmul, he'_tmul, map_one, Module.End.one_apply, map_smul]
        | add x y hx hy => simp only [map_add, hx, hy])⟩
    exact GlobalTheory.ProdLength.hasFiniteLength_of_injective Fi hFinj
      (GlobalTheory.SmGL.hasFiniteLength_of_isIrreducible (σ 0).rep.irr)

theorem finLen (hc : Continuous ψ) (h1 : ψ ≠ 1) (Mr : Representation ℂ (GL (Fin n) k × GL (Fin t) k) V)
    (hMs : IsSmooth Mr) (hM : HasFiniteLength Mr) :
    HasFiniteLength (twAct Mr (rightUnip k n t) (rightWhit k ψ n t) (MonoidHom.inl _ _) (inl_stab ψ n t)) := by
  obtain ⟨hgt, hlt⟩ := (hasFiniteLength_iff_wellFounded Mr).1 hM
  have key : ∀ S T : Subrepresentation Mr, T ≤ S →
      HasFiniteLength (twAct (subQuot S T) (rightUnip k n t) (rightWhit k ψ n t) (MonoidHom.inl _ _)
        (inl_stab ψ n t)) := by
    intro S₀
    refine WellFoundedLT.induction (motive := fun S => ∀ T, T ≤ S →
      HasFiniteLength (twAct (subQuot S T) (rightUnip k n t) (rightWhit k ψ n t) (MonoidHom.inl _ _)
        (inl_stab ψ n t))) S₀ ?_
    intro S ihS T₀
    refine WellFoundedGT.induction (motive := fun T => T ≤ S →
      HasFiniteLength (twAct (subQuot S T) (rightUnip k n t) (rightWhit k ψ n t) (MonoidHom.inl _ _)
        (inl_stab ψ n t))) T₀ ?_
    intro T ihT hTS
    rcases eq_or_lt_of_le hTS with hEq | hlt'
    · subst hEq
      haveI := GlobalTheory.ParIndExact.subsingleton_subQuot_self T
      haveI := subsingleton_tw (ρ := subQuot T T) (rightUnip k n t) (rightWhit k ψ n t)
      exact GlobalTheory.ProdLength.hasFiniteLength_of_subsingleton _
    by_cases hcov : T ⋖ S
    · exact base ψ hc h1 _ ((GlobalTheory.ParIndExact.isSubquotient_subQuot S T).isSmooth hMs)
        (GlobalTheory.SmGL.isIrreducible_subQuot hcov)
    obtain ⟨U, hTU, hUS⟩ : ∃ U, T < U ∧ U < S := by
      by_contra hno
      exact hcov ⟨hlt', fun U h1' h2' => hno ⟨U, h1', h2'⟩⟩
    obtain ⟨ι, p, -, hp, -, hex⟩ := GlobalTheory.ParIndExact.subQuot_exact (ρ := Mr) hTU.le hUS.le
    exact GlobalTheory.ProdLength.hasFiniteLength_of_exact (dMap _ _ _ _ ι) (dMap _ _ _ _ p)
      (d_exact _ _ _ _ ι p hp hex) (ihS U hUS T hTU.le) (ihT U hTU hUS.le)
  exact GlobalTheory.JacquetBlocks.hasFiniteLength_of_surjective (dMap _ _ _ _ (topBot Mr))
    (dMap_surjective _ _ _ _ _ (topBot_surjective Mr)) (key ⊤ ⊥ bot_le)

end Base

end PositivityTheory.RgGu.NR.DerFin

namespace PositivityTheory.RgGu.NR

open PositivityTheory.RgGu.NR.DerFin

theorem derFin_of (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (h : DerEquiv k) : DerFin k := by
  intro ψ hc h1 n j V _ _ π hs hi
  obtain ⟨E⟩ := h ψ n j V π
  have hfl : HasFiniteLength π := GlobalTheory.SmGL.hasFiniteLength_of_isIrreducible hi
  have hJ : HasFiniteLength (jac (two (stdSum (show n + (j + 1) = n + j + 1 from rfl))) π) :=
    (GlobalTheory.CompanionTheory.Published.bernsteinZelevinskyFiniteness k).2.1 _ _ _ _ V π hs hfl
  have hJU : HasFiniteLength (jacU₂ (stdSum (show n + (j + 1) = n + j + 1 from rfl)) π) :=
    (hasFiniteLength_comp_iff _ _ (leviTwo k (Fin n) (Fin (j + 1))).surjective).2
      ((GlobalTheory.JacquetBlocks.hasFiniteLength_twist_iff _ _).1 hJ)
  have hJs : IsSmooth (jacU₂ (stdSum (show n + (j + 1) = n + j + 1 from rfl)) π) :=
    isSmooth_comp (isSmooth_jacU _ hs) _ (continuous_leviTwo k)
  exact HasFiniteLength.of_equiv (finLen ψ hc h1 _ hJs hJU) E.symm

end PositivityTheory.RgGu.NR

import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.TateDefs
import ReciprocityTheory.GroupCohomology.ImportsAlt

open Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal TensorProduct Module UpperTheory.V.Loc Topology

section
open ReciprocityTheory.Coh
variable {l : ℕ} [Fact l.Prime] {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] {n : ℕ}

private noncomputable def redT (ρ : Representation ℤ_[l] G (Fin n → ℤ_[l])) (h : ContAction ρ) (m : ℕ) :
    TRep ℤ_[l] G :=
  { V := (Fin n → ℤ_[l]) ⧸ lSub l (Fin n → ℤ_[l]) (m + 1)
    ccs := ⟨fun _ => continuous_of_discreteTopology⟩
    rho := redRep ρ (m + 1)
    cont := contAction_redRep h (m + 1) }

private instance redT_disc (ρ : Representation ℤ_[l] G (Fin n → ℤ_[l])) (h : ContAction ρ) (m : ℕ) :
    DiscreteTopology (redT ρ h m).V := discrete_quot_lSub l n (m + 1)

private instance redT_fin (ρ : Representation ℤ_[l] G (Fin n → ℤ_[l])) (h : ContAction ρ) (m : ℕ) :
    Finite (redT ρ h m).V := finite_quot_lSub l n (m + 1)

private theorem lSub_le {X : Type} [AddCommGroup X] [Module ℤ_[l] X] (m : ℕ) :
    lSub l X (m + 1) ≤ (lSub l X m).comap LinearMap.id := by
  intro x hx
  obtain ⟨y, rfl⟩ := mem_lSub.mp hx
  show (l : ℤ_[l]) ^ (m + 1) • y ∈ lSub l X m
  exact mem_lSub.mpr ⟨(l : ℤ_[l]) • y, by rw [pow_succ, mul_smul]⟩

private noncomputable def tauL (l : ℕ) [Fact l.Prime] (X : Type) [AddCommGroup X] [Module ℤ_[l] X] (m : ℕ) :
    (X ⧸ lSub l X (m + 1)) →ₗ[ℤ_[l]] (X ⧸ lSub l X m) :=
  Submodule.mapQ _ _ LinearMap.id (lSub_le m)

private theorem tauL_mk {X : Type} [AddCommGroup X] [Module ℤ_[l] X] (m : ℕ) (x : X) :
    tauL l X m (Submodule.Quotient.mk x) = Submodule.Quotient.mk x := rfl

omit [TopologicalSpace G] [IsTopologicalGroup G] in
private theorem tauL_equiv {X : Type} [AddCommGroup X] [Module ℤ_[l] X] (ρ : Representation ℤ_[l] G X) (m : ℕ)
    (g : G) (y : X ⧸ lSub l X (m + 1)) : tauL l X m (redRep ρ (m + 1) g y) = redRep ρ m g (tauL l X m y) := by
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  rw [redRep_mk, tauL_mk, tauL_mk, redRep_mk]

private theorem tauL_surj {X : Type} [AddCommGroup X] [Module ℤ_[l] X] (m : ℕ) :
    Function.Surjective (tauL l X m) := by
  intro y
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  exact ⟨Submodule.Quotient.mk x, rfl⟩

private noncomputable def tauT (ρ : Representation ℤ_[l] G (Fin n → ℤ_[l])) (h : ContAction ρ) (m : ℕ) :
    Pair (redT ρ h (m + 1)) (redT ρ h m) :=
  Pair.ofMap (M := redT ρ h (m + 1)) (M' := redT ρ h m)
    (tauL l (Fin n → ℤ_[l]) (m + 1)) continuous_of_discreteTopology (tauL_equiv ρ (m + 1))

private noncomputable def piT (ρ : Representation ℤ_[l] G (Fin n → ℤ_[l])) (h : ContAction ρ) (m : ℕ) :
    Pair ({ V := Fin n → ℤ_[l], rho := ρ, cont := h } : TRep ℤ_[l] G) (redT ρ h m) :=
  Pair.ofMap (M := ({ V := Fin n → ℤ_[l], rho := ρ, cont := h } : TRep ℤ_[l] G)) (M' := redT ρ h m)
    (lSub l (Fin n → ℤ_[l]) (m + 1)).mkQ (continuous_mkQ _) (fun g x => (redRep_mk ρ (m + 1) g x).symm)

private theorem eq_zero_of_lSub (x : Fin n → ℤ_[l]) (hx : ∀ m, x ∈ lSub l (Fin n → ℤ_[l]) (m + 1)) : x = 0 := by
  funext i
  apply PadicInt.ext_of_toZModPow.mp
  intro k
  rw [Pi.zero_apply, map_zero]
  cases k with
  | zero =>
    haveI : Subsingleton (ZMod (l ^ 0)) := ZMod.subsingleton_iff.mpr (pow_zero _)
    exact Subsingleton.elim _ _
  | succ k => exact mem_lSub_pi.mp (hx k) i

private theorem towerLim (ρ : Representation ℤ_[l] G (Fin n → ℤ_[l])) (h : ContAction ρ) :
    Cx.IsTowerLim (fun m => (redT ρ h m).coch) (fun m => (tauT ρ h m).hom)
      (TRep.coch ({ V := Fin n → ℤ_[l], rho := ρ, cont := h } : TRep ℤ_[l] G)) fun m => (piT ρ h m).hom := by
  refine limRep_holds ℤ_[l] G (fun m => redT ρ h m) (tauT ρ h) _ (piT ρ h)
    (fun m => ⟨rfl, rfl, tauL_surj (m + 1), fun x => rfl⟩) ?_ ?_
  · have hc : Continuous fun (x : Fin n → ℤ_[l]) (m : ℕ) => (piT ρ h m).u x :=
      continuous_pi fun m => (piT ρ h m).u_cont
    refine (hc.isClosedEmbedding ?_).isEmbedding
    intro x y hxy
    rw [← sub_eq_zero]
    apply eq_zero_of_lSub
    intro m
    have := congr_fun hxy m
    exact (Submodule.Quotient.eq _).mp this
  · intro y hy
    let S : ℕ → Set (Fin n → ℤ_[l]) := fun m => (piT ρ h m).u ⁻¹' {y m}
    have hS : (⋂ m, S m).Nonempty := by
      apply IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed S
      · intro m x hx
        show (piT ρ h m).u x = y m
        have hx' : (piT ρ h (m + 1)).u x = y (m + 1) := hx
        rw [← hy m, ← hx']
        rfl
      · intro m
        obtain ⟨x, hx⟩ := Submodule.Quotient.mk_surjective _ (y m)
        exact ⟨x, hx⟩
      · exact isCompact_univ.of_isClosed_subset
          ((isClosed_singleton).preimage (piT ρ h 0).u_cont) (Set.subset_univ _)
      · intro m
        exact (isClosed_singleton).preimage (piT ρ h m).u_cont
    obtain ⟨x, hx⟩ := hS
    exact ⟨x, fun m => Set.mem_iInter.mp hx m⟩

private theorem smul_emb (m : ℕ) : IsEmbedding fun x : Fin n → ℤ_[l] => (l : ℤ_[l]) ^ m • x := by
  have hc : (l : ℤ_[l]) ^ m ≠ 0 :=
    pow_ne_zero _ (Nat.cast_ne_zero.mpr (Fact.out : l.Prime).ne_zero)
  refine (Continuous.isClosedEmbedding (continuous_const_smul _) ?_).isEmbedding
  intro x y hxy
  funext i
  have := congr_fun hxy i
  simp only [Pi.smul_apply, smul_eq_mul] at this
  exact mul_left_cancel₀ hc this

private theorem finH {χ : G →* ℤ_[l]ˣ} {d : ℕ} (hF : FinLevel l G χ d) (M : TRep ℤ_[l] G) [Finite M.V]
    [DiscreteTopology M.V] : (∀ k, Finite (M.H k)) ∧ ∀ k, 2 < k → Subsingleton (M.H k) := by
  obtain ⟨h1, h2, h3, -, -⟩ := hF M.V M.rho M.cont
  obtain ⟨hN, ⟨e0, -⟩, ⟨e1, -⟩, ⟨e2, -⟩⟩ := low_holds ℤ_[l] G M
  refine ⟨fun k => ?_, fun k hk => ?_⟩
  · match k with
    | 0 => exact Finite.of_equiv _ e0.symm.toEquiv
    | 1 => exact Finite.of_equiv _ e1.symm.toEquiv
    | 2 => exact Finite.of_equiv _ e2.symm.toEquiv
    | k + 3 =>
      obtain ⟨e, -⟩ := hN (k + 3)
      haveI := h3 (k + 3) (by omega)
      exact Finite.of_equiv _ e.symm.toEquiv
  · obtain ⟨e, -⟩ := hN k
    haveI := h3 k (by omega)
    exact e.toEquiv.subsingleton

end

theorem UpperTheory.latticeCochains_finGen_of_finLevel :
    ∀ {l : ℕ} [Fact l.Prime] {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] {χ : G →* ℤ_[l]ˣ} {d : ℕ}, FinLevel l G χ d → ∀ {n : ℕ} (ρ : Representation ℤ_[l] G (Fin n → ℤ_[l])) (h : ContAction ρ), ReciprocityTheory.Coh.Cx.FinGen (ReciprocityTheory.Coh.TRep.coch ({ V := Fin n → ℤ_[l], rho := ρ, cont := h } : ReciprocityTheory.Coh.TRep ℤ_[l] G)) 2 := by
  intro l _ G _ _ _ χ d hF n ρ h
  haveI : IsAdicComplete (Ideal.span {(l : ℤ_[l])}) ℤ_[l] :=
    PadicInt.maximalIdeal_eq_span_p (p := l) ▸ inferInstance
  have hl : (l : ℤ_[l]) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : l.Prime).ne_zero
  have hT := towerLim ρ h
  have htors : ∀ (k : ℕ) (x : (ReciprocityTheory.Coh.TRep.coch ({ V := Fin n → ℤ_[l], rho := ρ, cont := h } : ReciprocityTheory.Coh.TRep ℤ_[l] G)).X k),
      (l : ℤ_[l]) • x = 0 → x = 0 := by
    intro k x hx
    apply Subtype.ext
    funext g
    have := congr_arg (fun z : (ReciprocityTheory.Coh.TRep.coch ({ V := Fin n → ℤ_[l], rho := ρ, cont := h } : ReciprocityTheory.Coh.TRep ℤ_[l] G)).X k =>
      z.1 g) hx
    exact (smul_eq_zero.mp this).resolve_left hl
  have hker : ∀ (m k : ℕ) (x : (ReciprocityTheory.Coh.TRep.coch ({ V := Fin n → ℤ_[l], rho := ρ, cont := h } : ReciprocityTheory.Coh.TRep ℤ_[l] G)).X k),
      ((piT ρ h m).hom.f k) x = 0 ↔ ∃ y, x = (l : ℤ_[l]) ^ (m + 1) • y := by
    intro m k x
    have key : ((piT ρ h m).hom.f k) x = 0 ↔
        ∀ g, x.1 g ∈ lSub l (Fin n → ℤ_[l]) (m + 1) := by
      constructor
      · intro hx g
        have := congr_arg (fun z : (ReciprocityTheory.Coh.TRep.coch (redT ρ h m)).X k =>
          z.1 g) hx
        exact (Submodule.Quotient.mk_eq_zero _).mp this
      · intro hx
        apply Subtype.ext
        funext g
        exact (Submodule.Quotient.mk_eq_zero _).mpr (hx g)
    rw [key]
    constructor
    · intro hx
      choose y hy using fun g => mem_lSub.mp (hx g)
      have hyc : Continuous y := by
        apply (smul_emb (n := n) (l := l) (m + 1)).continuous_iff.mpr
        have : (fun x : Fin n → ℤ_[l] => (l : ℤ_[l]) ^ (m + 1) • x) ∘ y =
            x.1 := funext hy
        rw [this]
        exact x.2
      refine ⟨⟨y, hyc⟩, ?_⟩
      apply Subtype.ext
      funext g
      exact (hy g).symm
    · rintro ⟨y, rfl⟩ g
      exact mem_lSub.mpr ⟨y.1 g, rfl⟩
  have hfin : ∀ m, (∀ k, Finite ((redT ρ h m).H k)) ∧ ∀ k, 2 < k → Subsingleton ((redT ρ h m).H k) :=
    fun m => finH hF (redT ρ h m)
  have hlen0 : ∀ k, IsFiniteLength ℤ_[l] ((redT ρ h 0).coch.H k) := fun k => by
    haveI := (hfin 0).1 k
    exact isFiniteLength_iff_isNoetherian_isArtinian.mpr ⟨inferInstance, inferInstance⟩
  have res := ReciprocityTheory.Coh.finGen_holds ℤ_[l] (l : ℤ_[l]) _ _ _ _ hT htors hker hlen0
  refine ⟨fun k => (res k).1, fun k hk => ?_⟩
  have ext := (ReciprocityTheory.Coh.tower_holds ℤ_[l] _ _ _ _ hT k).2 (fun j _ m => by
    haveI := (hfin m).1 j
    infer_instance)
  refine ⟨fun a b => ?_⟩
  have ha := ext a (fun m => by
    haveI := (hfin m).2 k hk
    exact Subsingleton.elim _ _)
  have hb := ext b (fun m => by
    haveI := (hfin m).2 k hk
    exact Subsingleton.elim _ _)
  rw [ha, hb]

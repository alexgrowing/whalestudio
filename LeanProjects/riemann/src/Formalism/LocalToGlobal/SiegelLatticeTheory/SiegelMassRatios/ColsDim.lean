import Mathlib
import Formalism.SatakeDualWeyl.Statement
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.RationalPointsLeHolds
import Formalism.LocalToGlobal.SiegelLatticeTheory.SiegelMassRatios.ClassAct

noncomputable section

open Module IsDedekindDomain

namespace Formalism.L2.SG.ColsDim

open Formalism.UG

section Abstract

variable {Γ Gi Gf : Type} [Group Γ] [Group Gi] [Group Gf]

def StabTriv (ιf : Γ →* Gf) (K : Subgroup Gf) : Prop :=
  ∀ x : Gf, ∀ γ : Γ, x⁻¹ * ιf γ * x ∈ K → γ = 1

abbrev Classes (ιf : Γ →* Gf) (K : Subgroup Gf) : Type := ClassSet ιf.range K

def Forms (k : Type) [Field k] (ιi : Γ →* Gi) (ιf : Γ →* Gf) (K : Subgroup Gf) (ψ : K →* kˣ) :
    Submodule k (Gi × Gf → k) where
  carrier := {φ | (∀ γ : Γ, ∀ y : Gi × Gf, φ ((ιi γ, ιf γ) * y) = φ y) ∧
    ∀ y : Gi × Gf, ∀ κ : K, φ (y * (1, (κ : Gf))) = (ψ κ : k) * φ y}
  zero_mem' := ⟨fun _ _ => rfl, fun _ _ => by simp⟩
  add_mem' := by
    rintro f g ⟨hf1, hf2⟩ ⟨hg1, hg2⟩
    exact ⟨fun γ y => by simp [hf1 γ y, hg1 γ y], fun y κ => by simp [hf2 y κ, hg2 y κ, mul_add]⟩
  smul_mem' := by
    rintro c f ⟨hf1, hf2⟩
    exact ⟨fun γ y => by simp [hf1 γ y], fun y κ => by simp [hf2 y κ]; ring⟩

def Cols (k : Type) [Field k] {V : Type} [AddCommGroup V] [Module k V] (ιi : Γ →* Gi)
    (ιf : Γ →* Gf) (K : Subgroup Gf) (ψ : K →* kˣ) (π : Representation k Gi V) :
    Submodule k (V →ₗ[k] (Gi × Gf → k)) where
  carrier := {T | (∀ ξ : V, T ξ ∈ Forms k ιi ιf K ψ) ∧
    ∀ h : Gi, ∀ ξ : V, ∀ y : Gi × Gf, T (π h ξ) y = T ξ (y * (h, 1))}
  zero_mem' := ⟨fun _ => (Forms k ιi ιf K ψ).zero_mem, fun _ _ _ => rfl⟩
  add_mem' := by
    rintro S T ⟨hS1, hS2⟩ ⟨hT1, hT2⟩
    exact ⟨fun ξ => (Forms k ιi ιf K ψ).add_mem (hS1 ξ) (hT1 ξ),
      fun h ξ y => by simp [hS2 h ξ y, hT2 h ξ y]⟩
  smul_mem' := by
    rintro c T ⟨hT1, hT2⟩
    exact ⟨fun ξ => (Forms k ιi ιf K ψ).smul_mem c (hT1 ξ), fun h ξ y => by simp [hT2 h ξ y]⟩

def Equi (k : Type) [Field k] {W : Type} [AddCommGroup W] [Module k W] (ιf : Γ →* Gf)
    (K : Subgroup Gf) (ρ : Representation k Γ W) (χ : K →* kˣ) : Submodule k (Gf → W) where
  carrier := {f | ∀ γ : Γ, ∀ x : Gf, ∀ κ : K, f (ιf γ * x * κ) = (χ κ : k) • ρ γ (f x)}
  zero_mem' := by intro γ x κ; simp
  add_mem' := by intro f g hf hg γ x κ; simp [hf γ x κ, hg γ x κ]
  smul_mem' := by intro c f hf γ x κ; simp [hf γ x κ, smul_comm c]

def Sharp (k : Type) [Field k] {V : Type} [AddCommGroup V] [Module k V] (ιi : Γ →* Gi)
    (ιf : Γ →* Gf) (K : Subgroup Gf) (π : Representation k Gi V) (ψ : K →* kˣ) :
    Submodule k (Gf → V) :=
  Equi k ιf K (π.comp ιi) ψ⁻¹

end Abstract

def ColsDecomp : Prop :=
  ∀ (Γ Gi Gf : Type) [Group Γ] [Group Gi] [Group Gf] (k : Type) [Field k] (V : Type)
    [AddCommGroup V] [Module k V] (ιi : Γ →* Gi) (ιf : Γ →* Gf) (K : Subgroup Gf)
    (ψ : K →* kˣ) (π : Representation k Gi V) (s : Classes ιf K → Gf),
    (∀ c, DoubleCoset.mk ιf.range K (s c) = c) → StabTriv ιf K →
    ∃ e : Cols k ιi ιf K ψ π ≃ₗ[k] (Classes ιf K → Dual k V),
      ∀ T c ξ, e T c ξ = (T : V →ₗ[k] (Gi × Gf → k)) ξ (1, s c)

def ColsDim : Prop :=
  ∀ (Γ Gi Gf : Type) [Group Γ] [Group Gi] [Group Gf] (k : Type) [Field k] (V : Type)
    [AddCommGroup V] [Module k V] (ιi : Γ →* Gi) (ιf : Γ →* Gf) (K K0 : Subgroup Gf)
    (ψ : K →* kˣ) (π : Representation k Gi V),
    K ≤ K0 → StabTriv ιf K0 → Finite (Classes ιf K) → FiniteDimensional k V →
    FiniteDimensional k (Cols k ιi ιf K ψ π) ∧
      finrank k (Cols k ιi ιf K ψ π) = finrank k V * Nat.card (Classes ιf K)

def SharpDim : Prop :=
  ∀ (Γ Gi Gf : Type) [Group Γ] [Group Gi] [Group Gf] (k : Type) [Field k] (V : Type)
    [AddCommGroup V] [Module k V] (ιi : Γ →* Gi) (ιf : Γ →* Gf) (K K0 : Subgroup Gf)
    (ψ : K →* kˣ) (π : Representation k Gi V),
    K ≤ K0 → StabTriv ιf K0 → Finite (Classes ιf K) → FiniteDimensional k V →
    FiniteDimensional k (Sharp k ιi ιf K π ψ) ∧
      finrank k (Sharp k ιi ιf K π ψ) = finrank k V * Nat.card (Classes ιf K)

def SharpBij : Prop :=
  ∀ (Γ Gi Gf : Type) [Group Γ] [Group Gi] [Group Gf] (V : Type) [NormedAddCommGroup V]
    [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] (ιi : Γ →* Gi) (ιf : Γ →* Gf)
    (K : Subgroup Gf) (ψ : K →* ℂˣ) (π : Representation ℂ Gi V),
    (∀ h : Gi, ∀ v w : V, inner ℂ (π h v) (π h w) = inner ℂ v w) →
    (∀ κ : K, ‖((ψ κ : ℂˣ) : ℂ)‖ = 1) →
    ∃ e : Cols ℂ ιi ιf K ψ π ≃ Sharp ℂ ιi ιf K π ψ,
      (∀ (T : Cols ℂ ιi ιf K ψ π) (x : Gf) (ξ : V),
        (T : V →ₗ[ℂ] (Gi × Gf → ℂ)) ξ (1, x) = inner ℂ ((e T : Gf → V) x) ξ) ∧
      ∀ (c : ℂ) (T : Cols ℂ ιi ιf K ψ π), (e (c • T) : Gf → V) = (starRingEnd ℂ c) • (e T : Gf → V)

section Unitary

open NumberField

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]
  {n : Type} [Fintype n] [DecidableEq n]

theorem bc_mem_UPts (σ : E →ₐ[F] E) (J : Matrix n n E) (R : Type) [CommRing R] [Algebra F R]
    (g : UJ (σ : E →+* E) J) : bc (inclE (F := F) R) (g : GL n E) ∈ UPts σ J R := by
  have hg : cT (σ : E →+* E) ((g : GL n E) : Matrix n n E) * J * ((g : GL n E) : Matrix n n E) = J := g.2
  show cT (sigR σ R) ((inclE (F := F) R).mapMatrix ((g : GL n E) : Matrix n n E)) * J.map (inclE (F := F) R) *
    (inclE (F := F) R).mapMatrix ((g : GL n E) : Matrix n n E) = J.map (inclE (F := F) R)
  have key : cT (sigR σ R) ((inclE (F := F) R).mapMatrix ((g : GL n E) : Matrix n n E)) =
      (inclE (F := F) R).mapMatrix (cT (σ : E →+* E) ((g : GL n E) : Matrix n n E)) := by
    first
    | (unfold cT; ext i j; simp [sigR, inclE]; done)
    | (unfold cT; ext i j; simp [sigR, inclE, Matrix.conjTranspose_apply]; done)
    | (unfold cT sigR inclE; done)
  rw [key]
  have h2 := congrArg (inclE (F := F) R).mapMatrix hg
  simpa only [map_mul, RingHom.mapMatrix_apply] using h2

def ratHom (σ : E →ₐ[F] E) (J : Matrix n n E) (R : Type) [CommRing R] [Algebra F R] :
    UJ (σ : E →+* E) J →* UPts σ J R :=
  ((bc (inclE (F := F) R)).comp (UJ (σ : E →+* E) J).subtype).codRestrict _
    (fun g => bc_mem_UPts σ J R g)

abbrev Ginf (σ : E →ₐ[F] E) (J : Matrix n n E) := UPts σ J (InfiniteAdeleRing F)

abbrev Gfin (σ : E →ₐ[F] E) (J : Matrix n n E) := UPts σ J (FiniteAdeleRing (𝓞 F) F)

end Unitary

open NumberField in

def ColsDimU : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [Algebra F E] (n : Type) [Fintype n]
    [DecidableEq n] (σ : E →ₐ[F] E) (J : Matrix n n E) (K K0 : Subgroup (Gfin σ J))
    (ψ : K →* ℂˣ) (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (Ginf σ J) V),
    K ≤ K0 → StabTriv (ratHom σ J (FiniteAdeleRing (𝓞 F) F)) K0 →
    Finite (Classes (ratHom σ J (FiniteAdeleRing (𝓞 F) F)) K) → FiniteDimensional ℂ V →
    FiniteDimensional ℂ (Cols ℂ (ratHom σ J (InfiniteAdeleRing F))
        (ratHom σ J (FiniteAdeleRing (𝓞 F) F)) K ψ π) ∧
      finrank ℂ (Cols ℂ (ratHom σ J (InfiniteAdeleRing F)) (ratHom σ J (FiniteAdeleRing (𝓞 F) F))
          K ψ π) = finrank ℂ V * Nat.card (Classes (ratHom σ J (FiniteAdeleRing (𝓞 F) F)) K)

section Proofs

variable {Γ Gi Gf : Type} [Group Γ] [Group Gi] [Group Gf] (ιf : Γ →* Gf) (K : Subgroup Gf)

theorem mem_Equi {k : Type} [Field k] {W : Type} [AddCommGroup W] [Module k W]
    (ρ : Representation k Γ W) (χ : K →* kˣ) (f : Gf → W) :
    f ∈ Equi k ιf K ρ χ ↔ ∀ γ : Γ, ∀ x : Gf, ∀ κ : K, f (ιf γ * x * κ) = (χ κ : k) • ρ γ (f x) := Iff.rfl

theorem stabTriv_mono {K K0 : Subgroup Gf} (h : K ≤ K0) (hs : StabTriv ιf K0) : StabTriv ιf K := fun x γ hx => hs x γ (h hx)

theorem equi_subtype {k : Type} [Field k] {W : Type} [AddCommGroup W] [Module k W]
    (Γ' : Subgroup Gf) (ρ : Representation k Γ' W) (χ : K →* kˣ) :
    Equi k Γ'.subtype K ρ χ = Formalism.L2.SG.ClassAct.AMFChi k Γ' K ρ χ := rfl

theorem exists_dec (s : Classes ιf K → Gf) (hs : ∀ c, DoubleCoset.mk ιf.range K (s c) = c)
    (g : Gf) : ∃ p : Γ × K, g = ιf p.1 * s (DoubleCoset.mk ιf.range K g) * (p.2 : Gf) := by
  obtain ⟨h, hh, κ, hκ, e⟩ := (DoubleCoset.eq _ _ _ _).1 (hs (DoubleCoset.mk ιf.range K g))
  obtain ⟨γ, rfl⟩ := MonoidHom.mem_range.1 hh
  exact ⟨(γ, ⟨κ, hκ⟩), e⟩

theorem dec_unique (hst : StabTriv ιf K) (x : Gf) (γ γ' : Γ) (κ κ' : K)
    (e : ιf γ * x * κ = ιf γ' * x * κ') : γ = γ' ∧ κ = κ' := by
  have h1 : x⁻¹ * ιf (γ'⁻¹ * γ) * x = (κ' : Gf) * (κ : Gf)⁻¹ := by
    rw [map_mul, map_inv]
    calc x⁻¹ * ((ιf γ')⁻¹ * ιf γ) * x = (ιf γ' * x)⁻¹ * (ιf γ * x * κ) * (κ : Gf)⁻¹ := by group
      _ = (ιf γ' * x)⁻¹ * (ιf γ' * x * κ') * (κ : Gf)⁻¹ := by rw [e]
      _ = κ' * (κ : Gf)⁻¹ := by group
  have hmem : x⁻¹ * ιf (γ'⁻¹ * γ) * x ∈ K := by
    rw [h1]; exact K.mul_mem κ'.2 (K.inv_mem κ.2)
  have hγ : γ'⁻¹ * γ = 1 := hst x _ hmem
  rw [inv_mul_eq_one] at hγ
  subst hγ
  exact ⟨rfl, Subtype.ext (mul_left_cancel e)⟩

variable {k : Type} [Field k] {W : Type} [AddCommGroup W] [Module k W]

def extF (s : Classes ιf K → Gf) (hs : ∀ c, DoubleCoset.mk ιf.range K (s c) = c)
    (ρ : Representation k Γ W) (χ : K →* kˣ) (w : Classes ιf K → W) (g : Gf) : W :=
  ((χ (Classical.choose (exists_dec ιf K s hs g)).2 : kˣ) : k) •
    ρ (Classical.choose (exists_dec ιf K s hs g)).1 (w (DoubleCoset.mk ιf.range K g))

theorem extF_eq (hst : StabTriv ιf K) (s : Classes ιf K → Gf)
    (hs : ∀ c, DoubleCoset.mk ιf.range K (s c) = c) (ρ : Representation k Γ W) (χ : K →* kˣ)
    (w : Classes ιf K → W) (c : Classes ιf K) (g : Gf) (γ : Γ) (κ : K)
    (e : g = ιf γ * s c * κ) : extF ιf K s hs ρ χ w g = ((χ κ : kˣ) : k) • ρ γ (w c) := by
  have hc : DoubleCoset.mk ιf.range K g = c := by
    rw [e]
    exact ((DoubleCoset.eq _ _ _ _).2 ⟨(ιf γ)⁻¹, ιf.range.inv_mem (MonoidHom.mem_range.2 ⟨γ, rfl⟩),
      ((κ : K) : Gf)⁻¹, K.inv_mem κ.2, by group⟩).trans (hs c)
  have spec := Classical.choose_spec (exists_dec ιf K s hs g)
  unfold extF
  generalize Classical.choose (exists_dec ιf K s hs g) = p at spec ⊢
  rw [hc] at spec ⊢
  obtain ⟨h1, h2⟩ := dec_unique ιf K hst (s c) _ _ _ _ (spec.symm.trans e)
  rw [h1, h2]

theorem extF_mem (hst : StabTriv ιf K) (s : Classes ιf K → Gf)
    (hs : ∀ c, DoubleCoset.mk ιf.range K (s c) = c) (ρ : Representation k Γ W) (χ : K →* kˣ)
    (w : Classes ιf K → W) : extF ιf K s hs ρ χ w ∈ Equi k ιf K ρ χ := by
  rw [mem_Equi]
  intro γ x κ
  obtain ⟨p, hp⟩ := exists_dec ιf K s hs x
  have hx := extF_eq ιf K hst s hs ρ χ w _ x p.1 p.2 hp
  have hy := extF_eq ιf K hst s hs ρ χ w (DoubleCoset.mk ιf.range K x) (ιf γ * x * κ) (γ * p.1)
    (p.2 * κ) (by
      conv_lhs => rw [hp]
      simp only [map_mul, Subgroup.coe_mul, mul_assoc])
  rw [hy, hx, map_mul, map_mul, Units.val_mul, Module.End.mul_apply, map_smul, smul_smul, mul_comm]

def decEquiv (hst : StabTriv ιf K) (s : Classes ιf K → Gf)
    (hs : ∀ c, DoubleCoset.mk ιf.range K (s c) = c) (ρ : Representation k Γ W) (χ : K →* kˣ) :
    Equi k ιf K ρ χ ≃ₗ[k] (Classes ιf K → W) where
  toFun f c := (f : Gf → W) (s c)
  map_add' _ _ := by funext c; rfl
  map_smul' _ _ := by funext c; rfl
  invFun w := ⟨extF ιf K s hs ρ χ w, extF_mem ιf K hst s hs ρ χ w⟩
  left_inv f := by
    apply Subtype.ext
    funext g
    have spec := Classical.choose_spec (exists_dec ιf K s hs g)
    show extF ιf K s hs ρ χ (fun c => (f : Gf → W) (s c)) g = (f : Gf → W) g
    rw [extF_eq ιf K hst s hs ρ χ _ _ g _ _ spec, congrArg (f : Gf → W) spec,
      (mem_Equi ιf K ρ χ _).1 f.2]
  right_inv w := by
    funext c
    show extF ιf K s hs ρ χ w (s c) = w c
    rw [extF_eq ιf K hst s hs ρ χ w c (s c) 1 1 (by simp)]
    simp

private theorem exists_doubleCoset_section {Γ' Gf' : Type} [Group Γ'] [Group Gf'] (ιf' : Γ' →* Gf')
    (K' : Subgroup Gf') :
    ∃ s : Classes ιf' K' → Gf', ∀ c, DoubleCoset.mk ιf'.range K' (s c) = c :=
  ⟨fun c => Quotient.out c, fun c => Quotient.out_eq' c⟩

theorem equi_dim (hst : StabTriv ιf K) [Finite (Classes ιf K)] [FiniteDimensional k W]
    (ρ : Representation k Γ W) (χ : K →* kˣ) :
    FiniteDimensional k (Equi k ιf K ρ χ) ∧
      finrank k (Equi k ιf K ρ χ) = finrank k W * Nat.card (Classes ιf K) := by
  obtain ⟨s, hs⟩ := exists_doubleCoset_section ιf K
  haveI := Fintype.ofFinite (Classes ιf K)
  let e := decEquiv ιf K hst s hs ρ χ
  haveI : FiniteDimensional k (Equi k ιf K ρ χ) := LinearEquiv.finiteDimensional e.symm
  refine ⟨inferInstance, ?_⟩
  rw [e.finrank_eq, Module.finrank_pi_fintype, Finset.sum_const, Finset.card_univ, smul_eq_mul,
    Nat.card_eq_fintype_card, mul_comm]

variable {V : Type} [AddCommGroup V] [Module k V]

def dualRep (ιi : Γ →* Gi) (π : Representation k Gi V) : Representation k Γ (Dual k V) where
  toFun γ := (π (ιi γ⁻¹)).dualMap
  map_one' := by ext f ξ; simp
  map_mul' γ δ := by ext f ξ; simp [mul_inv_rev, map_mul, Module.End.mul_apply]

def toEqui (ιi : Γ →* Gi) (ψ : K →* kˣ) (π : Representation k Gi V)
    (T : Cols k ιi ιf K ψ π) (x : Gf) : Dual k V :=
  (LinearMap.proj ((1 : Gi), x)).comp (T : V →ₗ[k] (Gi × Gf → k))

theorem toEqui_mem (ιi : Γ →* Gi) (ψ : K →* kˣ) (π : Representation k Gi V)
    (T : Cols k ιi ιf K ψ π) : toEqui ιf K ιi ψ π T ∈ Equi k ιf K (dualRep ιi π) ψ := by
  obtain ⟨hT1, hT2⟩ := T.2
  rw [mem_Equi]
  intro γ x κ
  ext ξ
  obtain ⟨hF1, hF2⟩ := hT1 ξ
  have e1 : ((1 : Gi), ιf γ * x * (κ : Gf)) = ((1 : Gi), ιf γ * x) * (1, (κ : Gf)) := by simp
  have e2 : ((1 : Gi), ιf γ * x) = (ιi γ, ιf γ) * (ιi γ⁻¹, x) := by simp
  have e3 : (ιi γ⁻¹, x) = ((1 : Gi), x) * (ιi γ⁻¹, (1 : Gf)) := by simp
  show (T : V →ₗ[k] (Gi × Gf → k)) ξ (1, ιf γ * x * κ) =
    (ψ κ : k) * (T : V →ₗ[k] (Gi × Gf → k)) (π (ιi γ⁻¹) ξ) (1, x)
  rw [e1, hF2, e2, hF1, e3, ← hT2]

def ofEquiFun (ιi : Γ →* Gi) (π : Representation k Gi V) (f : Gf → Dual k V) :
    V →ₗ[k] (Gi × Gf → k) where
  toFun ξ y := f y.2 (π y.1 ξ)
  map_add' ξ η := by funext y; simp
  map_smul' c ξ := by funext y; simp

theorem ofEqui_mem (ιi : Γ →* Gi) (ψ : K →* kˣ) (π : Representation k Gi V)
    (f : Equi k ιf K (dualRep ιi π) ψ) : ofEquiFun ιi π (f : Gf → Dual k V) ∈ Cols k ιi ιf K ψ π := by
  have hf := (mem_Equi ιf K (dualRep ιi π) ψ _).1 f.2
  refine ⟨fun ξ => ⟨fun γ y => ?_, fun y κ => ?_⟩, fun h ξ y => ?_⟩
  · have := hf γ y.2 1
    simp only [OneMemClass.coe_one, mul_one, map_one, Units.val_one, one_smul] at this
    show (f : Gf → Dual k V) (ιf γ * y.2) (π (ιi γ * y.1) ξ) = (f : Gf → Dual k V) y.2 (π y.1 ξ)
    rw [this]
    show (f : Gf → Dual k V) y.2 (π (ιi γ⁻¹) (π (ιi γ * y.1) ξ)) = (f : Gf → Dual k V) y.2 (π y.1 ξ)
    rw [← Module.End.mul_apply, ← map_mul, map_inv, inv_mul_cancel_left]
  · have := hf 1 y.2 κ
    simp only [map_one, one_mul] at this
    show (f : Gf → Dual k V) (y.2 * κ) (π (y.1 * 1) ξ) = (ψ κ : k) * (f : Gf → Dual k V) y.2 (π y.1 ξ)
    rw [this, mul_one, Module.End.one_apply, LinearMap.smul_apply, smul_eq_mul]
  · show (f : Gf → Dual k V) y.2 (π y.1 (π h ξ)) = (f : Gf → Dual k V) (y.2 * 1) (π (y.1 * h) ξ)
    rw [mul_one, map_mul, Module.End.mul_apply]

def colsEquiv (ιi : Γ →* Gi) (ψ : K →* kˣ) (π : Representation k Gi V) :
    Cols k ιi ιf K ψ π ≃ₗ[k] Equi k ιf K (dualRep ιi π) ψ where
  toFun T := ⟨toEqui ιf K ιi ψ π T, toEqui_mem ιf K ιi ψ π T⟩
  map_add' _ _ := by apply Subtype.ext; funext x; ext ξ; rfl
  map_smul' _ _ := by apply Subtype.ext; funext x; ext ξ; rfl
  invFun f := ⟨ofEquiFun ιi π (f : Gf → Dual k V), ofEqui_mem ιf K ιi ψ π f⟩
  left_inv T := by
    apply Subtype.ext
    ext ξ y
    obtain ⟨_, hT2⟩ := T.2
    have e : y = ((1 : Gi), y.2) * (y.1, (1 : Gf)) := by simp [Prod.ext_iff]
    show (T : V →ₗ[k] (Gi × Gf → k)) (π y.1 ξ) (1, y.2) = (T : V →ₗ[k] (Gi × Gf → k)) ξ y
    rw [hT2, ← e]
  right_inv f := by
    apply Subtype.ext
    funext x
    ext ξ
    show (f : Gf → Dual k V) x (π 1 ξ) = (f : Gf → Dual k V) x ξ
    rw [map_one, Module.End.one_apply]

end Proofs

section SharpProof

open InnerProductSpace

variable {Γ Gi Gf : Type} [Group Γ] [Group Gi] [Group Gf] (ιf : Γ →* Gf) (K : Subgroup Gf)
  {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]

theorem conj_inv_norm_one (z : ℂ) (h : ‖z‖ = 1) : starRingEnd ℂ z⁻¹ = z := by
  have h2 : z * starRingEnd ℂ z = 1 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, h]; norm_num
  have h3 : starRingEnd ℂ z = z⁻¹ := eq_inv_of_mul_eq_one_right h2
  rw [← h3, Complex.conj_conj]

theorem inner_unitary (π : Representation ℂ Gi V)
    (hπ : ∀ h : Gi, ∀ v w : V, inner ℂ (π h v) (π h w) = inner ℂ v w) (h : Gi) (v w : V) :
    inner ℂ (π h v) w = inner ℂ v (π h⁻¹ w) := by
  have := hπ h v (π h⁻¹ w)
  rwa [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply] at this

def sharpFun (f : Gf → Dual ℂ V) (x : Gf) : V :=
  (toDual ℂ V).symm (LinearMap.toContinuousLinearMap (f x))

theorem inner_sharpFun (f : Gf → Dual ℂ V) (x : Gf) (ξ : V) :
    inner ℂ (sharpFun f x) ξ = f x ξ := by
  unfold sharpFun
  rw [toDual_symm_apply]
  rfl

theorem sharpFun_mem (ιi : Γ →* Gi) (ψ : K →* ℂˣ) (π : Representation ℂ Gi V)
    (hπ : ∀ h : Gi, ∀ v w : V, inner ℂ (π h v) (π h w) = inner ℂ v w)
    (hψ : ∀ κ : K, ‖((ψ κ : ℂˣ) : ℂ)‖ = 1) (f : Equi ℂ ιf K (dualRep ιi π) ψ) :
    sharpFun (f : Gf → Dual ℂ V) ∈ Sharp ℂ ιi ιf K π ψ := by
  have hf := (mem_Equi ιf K (dualRep ιi π) ψ _).1 f.2
  show _ ∈ Equi ℂ ιf K (π.comp ιi) ψ⁻¹
  rw [mem_Equi]
  intro γ x κ
  apply ext_inner_right ℂ
  intro ξ
  rw [inner_sharpFun, hf γ x κ, inner_smul_left, MonoidHom.inv_apply, Units.val_inv_eq_inv_val,
    conj_inv_norm_one _ (hψ κ), MonoidHom.comp_apply, inner_unitary π hπ, inner_sharpFun, ← map_inv]
  rfl

theorem innerFun_mem (ιi : Γ →* Gi) (ψ : K →* ℂˣ) (π : Representation ℂ Gi V)
    (hπ : ∀ h : Gi, ∀ v w : V, inner ℂ (π h v) (π h w) = inner ℂ v w)
    (hψ : ∀ κ : K, ‖((ψ κ : ℂˣ) : ℂ)‖ = 1) (φ : Sharp ℂ ιi ιf K π ψ) :
    (fun x => (innerₛₗ ℂ ((φ : Gf → V) x) : Dual ℂ V)) ∈ Equi ℂ ιf K (dualRep ιi π) ψ := by
  have hφ := (mem_Equi ιf K (π.comp ιi) ψ⁻¹ _).1 φ.2
  rw [mem_Equi]
  intro γ x κ
  ext ξ
  show inner ℂ ((φ : Gf → V) (ιf γ * x * κ)) ξ = (ψ κ : ℂ) * inner ℂ ((φ : Gf → V) x) (π (ιi γ⁻¹) ξ)
  rw [hφ γ x κ, inner_smul_left, MonoidHom.inv_apply, Units.val_inv_eq_inv_val,
    conj_inv_norm_one _ (hψ κ), MonoidHom.comp_apply, inner_unitary π hπ, ← map_inv ιi γ]

end SharpProof

open InnerProductSpace in
theorem sharp_bijective : SharpBij := by
  intro Γ Gi Gf _ _ _ V _ _ _ ιi ιf K ψ π hπ hψ
  let F : Equi ℂ ιf K (dualRep ιi π) ψ ≃ Sharp ℂ ιi ιf K π ψ :=
    { toFun := fun f => ⟨sharpFun (f : Gf → Module.Dual ℂ V), sharpFun_mem ιf K ιi ψ π hπ hψ f⟩
      invFun := fun φ => ⟨fun x => (innerₛₗ ℂ ((φ : Gf → V) x) : Module.Dual ℂ V),
        innerFun_mem ιf K ιi ψ π hπ hψ φ⟩
      left_inv := fun f => by
        apply Subtype.ext
        funext x
        ext ξ
        exact inner_sharpFun _ x ξ
      right_inv := fun φ => by
        apply Subtype.ext
        funext x
        apply ext_inner_right ℂ
        intro ξ
        exact inner_sharpFun _ x ξ }
  refine ⟨(colsEquiv ιf K ιi ψ π).toEquiv.trans F,
    fun T x ξ => (inner_sharpFun (toEqui ιf K ιi ψ π T) x ξ).symm, fun c T => ?_⟩
  funext x
  apply ext_inner_right ℂ
  intro ξ
  have h1 := inner_sharpFun (toEqui ιf K ιi ψ π (c • T)) x ξ
  have h2 := inner_sharpFun (toEqui ιf K ιi ψ π T) x ξ
  show inner ℂ (sharpFun (toEqui ιf K ιi ψ π (c • T)) x) ξ =
    inner ℂ ((starRingEnd ℂ c) • sharpFun (toEqui ιf K ιi ψ π T) x) ξ
  rw [h1, inner_smul_left, Complex.conj_conj, h2]
  rfl

theorem columns_decomposition : ColsDecomp := by
  intro Γ Gi Gf _ _ _ k _ V _ _ ιi ιf K ψ π s hs hst
  exact ⟨(colsEquiv ιf K ιi ψ π).trans (decEquiv ιf K hst s hs (dualRep ιi π) ψ), fun T c ξ => rfl⟩

theorem columns_dimension : ColsDim := by
  intro Γ Gi Gf _ _ _ k _ V _ _ ιi ιf K K0 ψ π hK hst hfin hV
  obtain ⟨h1, h2⟩ := equi_dim ιf K (stabTriv_mono ιf hK hst) (dualRep ιi π) ψ
  let e := colsEquiv ιf K ιi ψ π
  haveI := h1
  refine ⟨LinearEquiv.finiteDimensional e.symm, ?_⟩
  rw [e.finrank_eq, h2, Subspace.dual_finrank_eq]

theorem sharp_dimension : SharpDim := by
  intro Γ Gi Gf _ _ _ k _ V _ _ ιi ιf K K0 ψ π hK hst hfin hV
  exact equi_dim ιf K (stabTriv_mono ιf hK hst) (π.comp ιi) ψ⁻¹

theorem columns_dimension_unitary : ColsDimU := by
  intro F E _ _ _ _ n _ _ σ J K K0 ψ V _ _ π hK hst hfin hV
  exact columns_dimension _ _ _ ℂ V _ _ K K0 ψ π hK hst hfin hV

end Formalism.L2.SG.ColsDim

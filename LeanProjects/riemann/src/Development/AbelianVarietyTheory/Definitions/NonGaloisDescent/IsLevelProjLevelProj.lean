import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivMultiProdOne

noncomputable section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL
open scoped Topology

namespace GlobalTheory.LBC

section Groups

variable {k k' : Type} [Field k] [Field k'] [Algebra k k']

def galAct (s : k' ≃ₐ[k] k') (n : ℕ) : GL (Fin n) k' →* GL (Fin n) k' :=
  GeneralLinearGroup.map s.toAlgHom.toRingHom

@[simp] theorem galAct_apply (s : k' ≃ₐ[k] k') {n : ℕ} (g : GL (Fin n) k') (i j : Fin n) :
    (galAct s n g : Matrix (Fin n) (Fin n) k') i j = s ((g : Matrix (Fin n) (Fin n) k') i j) := rfl

@[simp] theorem galAct_one (n : ℕ) : galAct (1 : k' ≃ₐ[k] k') n = MonoidHom.id _ := by
  ext g i j; rfl

theorem galAct_mul (s t : k' ≃ₐ[k] k') (n : ℕ) : galAct (s * t) n = (galAct s n).comp (galAct t n) := by
  ext g i j; rfl

def incl (k' : Type) [Field k'] [Algebra k k'] (n : ℕ) : GL (Fin n) k →* GL (Fin n) k' :=
  GeneralLinearGroup.map (algebraMap k k')

@[simp] theorem incl_apply {n : ℕ} (γ : GL (Fin n) k) (i j : Fin n) :
    (incl k' n γ : Matrix (Fin n) (Fin n) k') i j = algebraMap k k' ((γ : Matrix (Fin n) (Fin n) k) i j) := rfl

@[simp] theorem galAct_incl (s : k' ≃ₐ[k] k') {n : ℕ} (γ : GL (Fin n) k) : galAct s n (incl k' n γ) = incl k' n γ := by
  ext i j; simp

variable (k) in

def norm (s : k' ≃ₐ[k] k') {n : ℕ} (g : GL (Fin n) k') : GL (Fin n) k' :=
  (List.ofFn fun j : Fin (Module.finrank k k') => galAct (s ^ (j : ℕ)) n g).prod

def IsStable (s : k' ≃ₐ[k] k') {n : ℕ} (K : Subgroup (GL (Fin n) k')) : Prop := K.map (galAct s n) = K

end Groups

section Traces

variable {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]

def IsLevelProj (π : Representation ℂ G V) (K : Subgroup G) (A : V →ₗ[ℂ] V)
    (T : fixed π K →ₗ[ℂ] fixed π K) : Prop :=
  ∀ v : fixed π K, ((T v : V) - A v) ∈ twKer π K 1

def HasLevelTrace (π : Representation ℂ G V) (K : Subgroup G) (A : V →ₗ[ℂ] V) (c : ℂ) : Prop :=
  FiniteDimensional ℂ (fixed π K) ∧ ∃ T, IsLevelProj π K A T ∧ LinearMap.trace ℂ _ T = c

theorem isLevelProj_id (π : Representation ℂ G V) (K : Subgroup G) :
    IsLevelProj π K LinearMap.id LinearMap.id := fun v => by simp

theorem hasLevelTrace_id (π : Representation ℂ G V) (K : Subgroup G) [FiniteDimensional ℂ (fixed π K)] :
    HasLevelTrace π K LinearMap.id (Module.finrank ℂ (fixed π K)) :=
  ⟨inferInstance, _, isLevelProj_id π K, LinearMap.trace_id ℂ _⟩

end Traces

section Unique

variable {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] {π : Representation ℂ G V} {K : Subgroup G}
  {A : V →ₗ[ℂ] V}

theorem IsLevelProj.unique (hd : Disjoint (fixed π K) (twKer π K 1)) {T T' : fixed π K →ₗ[ℂ] fixed π K}
    (hT : IsLevelProj π K A T) (hT' : IsLevelProj π K A T') : T = T' := by
  ext v
  have h1 : ((T v : V) - T' v) ∈ fixed π K := sub_mem (T v).2 (T' v).2
  have h2 : ((T v : V) - T' v) ∈ twKer π K 1 := by
    have := sub_mem (hT v) (hT' v)
    rwa [sub_sub_sub_cancel_right] at this
  exact sub_eq_zero.1 (Submodule.disjoint_def.1 hd _ h1 h2)

theorem HasLevelTrace.unique (hd : Disjoint (fixed π K) (twKer π K 1)) {c c' : ℂ} (h : HasLevelTrace π K A c)
    (h' : HasLevelTrace π K A c') : c = c' := by
  obtain ⟨_, T, hT, rfl⟩ := h
  obtain ⟨_, T', hT', rfl⟩ := h'
  rw [hT.unique hd hT']

def levelProj (hc : IsCompl (fixed π K) (twKer π K 1)) (A : V →ₗ[ℂ] V) : fixed π K →ₗ[ℂ] fixed π K :=
  Submodule.projectionOnto _ _ hc ∘ₗ A ∘ₗ (fixed π K).subtype

end Unique

section Lift

variable {k k' : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  [Field k'] [ValuativeRel k'] [TopologicalSpace k'] [IsNonarchimedeanLocalField k'] [Algebra k k']
  {n : ℕ} {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

variable (k) in

def IsTwInt (s : k' ≃ₐ[k] k') (P : Representation ℂ (GL (Fin n) k') W) (I : W →ₗ[ℂ] W) : Prop :=
  (∀ g, P (galAct s n g) ∘ₗ I = I ∘ₗ P g) ∧ 0 < Module.finrank k k' ∧ I ^ Module.finrank k k' = 1

theorem IsTwInt.isUnit {s : k' ≃ₐ[k] k'} {P : Representation ℂ (GL (Fin n) k') W} {I : W →ₗ[ℂ] W}
    (hI : IsTwInt k s P I) : IsUnit I :=
  IsUnit.of_pow_eq_one hI.2.2 hI.2.1.ne'

theorem IsTwInt.conj {s : k' ≃ₐ[k] k'} {P : Representation ℂ (GL (Fin n) k') W} {I : W →ₗ[ℂ] W}
    (hI : IsTwInt k s P I) (g : GL (Fin n) k') : P (galAct s n g) = I * P g * ((hI.isUnit.unit⁻¹ : (W →ₗ[ℂ] W)ˣ) : W →ₗ[ℂ] W) := by
  rw [Units.eq_mul_inv_iff_mul_eq, IsUnit.unit_spec]
  exact hI.1 g

theorem IsTwInt.mem_fixed {s : k' ≃ₐ[k] k'} {P : Representation ℂ (GL (Fin n) k') W} {I : W →ₗ[ℂ] W}
    (hI : IsTwInt k s P I) {K : Subgroup (GL (Fin n) k')} (hK : IsStable s K) {v : W} (hv : v ∈ fixed P K) :
    I v ∈ fixed P K := by
  intro x
  have hx : (x : GL (Fin n) k') ∈ K.map (galAct s n) := by rw [hK]; exact x.2
  obtain ⟨y, hy, e⟩ := Subgroup.mem_map.1 hx
  have h1 := LinearMap.congr_fun (hI.1 y) v
  simp only [LinearMap.comp_apply] at h1
  have h2 : P y v = v := by simpa using hv ⟨y, hy⟩
  simp only [MonoidHom.one_apply, Units.val_one, one_smul]
  rw [← e, h1, h2]

variable (k) in

def TwCharVal (s : k' ≃ₐ[k] k') (P : Representation ℂ (GL (Fin n) k') W) (I : W →ₗ[ℂ] W) (g' : GL (Fin n) k')
    (c : ℂ) : Prop :=
  ∃ U ∈ 𝓝 (1 : GL (Fin n) k'), ∀ K : Subgroup (GL (Fin n) k'), IsOpen (K : Set (GL (Fin n) k')) →
    IsCompact (K : Set (GL (Fin n) k')) → IsStable s K → (K : Set (GL (Fin n) k')) ⊆ U →
      HasLevelTrace P K (P g' ∘ₗ I) c

def CharVal (π : Representation ℂ (GL (Fin n) k) V) (γ : GL (Fin n) k) (c : ℂ) : Prop :=
  ∃ U ∈ 𝓝 (1 : GL (Fin n) k), ∀ K : Subgroup (GL (Fin n) k), IsOpen (K : Set (GL (Fin n) k)) →
    IsCompact (K : Set (GL (Fin n) k)) → (K : Set (GL (Fin n) k)) ⊆ U → HasLevelTrace π K (π γ) c

def IsLBC (s : k' ≃ₐ[k] k') (π : Representation ℂ (GL (Fin n) k) V) (P : Representation ℂ (GL (Fin n) k') W) :
    Prop :=
  IsSmooth π ∧ π.IsIrreducible ∧ IsSmooth P ∧ P.IsIrreducible ∧
  ∃ I : W →ₗ[ℂ] W, IsTwInt k s P I ∧
    ∀ g' : GL (Fin n) k', (norm k s g' : Matrix (Fin n) (Fin n) k').charpoly.Separable →
      ∀ γ : GL (Fin n) k, (γ : Matrix (Fin n) (Fin n) k).charpoly.map (algebraMap k k') =
          (norm k s g' : Matrix (Fin n) (Fin n) k').charpoly →
        ∃ c : ℂ, TwCharVal k s P I g' c ∧ CharVal π γ c

def IsLBCCl (s : k' ≃ₐ[k] k') (x : IrrGL k) (y : IrrGL k') : Prop :=
  ∃ (m : ℕ) (π : IrrRep (GL (Fin m) k)) (P : IrrRep (GL (Fin m) k')), x = ⟨m, π.cl⟩ ∧ y = ⟨m, P.cl⟩ ∧
    IsLBC s π.ρ P.ρ

theorem isTwInt_of_triv (s : k' ≃ₐ[k] k') (hd : 0 < Module.finrank k k') {P : Representation ℂ (GL (Fin n) k') ℂ}
    (hP : ∀ g, P g = LinearMap.id) : IsTwInt k s P LinearMap.id :=
  ⟨fun g => by rw [hP, hP], hd, one_pow _⟩

theorem hasLevelTrace_of_triv {G : Type} [Group G] {P : Representation ℂ G ℂ} (hP : ∀ g, P g = LinearMap.id)
    (K : Subgroup G) : HasLevelTrace P K LinearMap.id 1 := by
  have htop : fixed P K = ⊤ := by
    ext v; simp [fixed, eig, hP]
  have h1 : Module.finrank ℂ (fixed P K) = 1 := by
    rw [htop, finrank_top, Module.finrank_self]
  have := hasLevelTrace_id P K
  rwa [h1, Nat.cast_one] at this

theorem charVal_of_triv {P : Representation ℂ (GL (Fin n) k) ℂ} (hP : ∀ g, P g = LinearMap.id) (γ : GL (Fin n) k) :
    CharVal P γ 1 :=
  ⟨Set.univ, Filter.univ_mem, fun K _ _ _ => by rw [hP]; exact hasLevelTrace_of_triv hP K⟩

theorem twCharVal_of_triv (s : k' ≃ₐ[k] k') {P : Representation ℂ (GL (Fin n) k') ℂ} (hP : ∀ g, P g = LinearMap.id)
    (g' : GL (Fin n) k') : TwCharVal k s P LinearMap.id g' 1 :=
  ⟨Set.univ, Filter.univ_mem, fun K _ _ _ _ => by rw [hP]; exact hasLevelTrace_of_triv hP K⟩

theorem ofChar_one_apply {G : Type} [Group G] (g : G) : SmGL.ofChar (1 : G →* ℂˣ) g = LinearMap.id := by
  ext; simp [SmGL.ofChar]

theorem isLBC_one (s : k' ≃ₐ[k] k') (hd : 0 < Module.finrank k k') :
    IsLBC s (SmGL.ofChar (1 : GL (Fin n) k →* ℂˣ)) (SmGL.ofChar (1 : GL (Fin n) k' →* ℂˣ)) :=
  ⟨(isSmooth_ofChar_iff _).2 isSmoothChar_one, isIrreducible_ofChar _,
    (isSmooth_ofChar_iff _).2 isSmoothChar_one, isIrreducible_ofChar _, LinearMap.id,
    isTwInt_of_triv s hd ofChar_one_apply, fun g' _ γ _ =>
      ⟨1, twCharVal_of_triv s ofChar_one_apply g', charVal_of_triv ofChar_one_apply γ⟩⟩

end Lift

example {k k' : Type} [Field k] [Field k'] [Algebra k k'] {n : ℕ} (g : GL (Fin n) k') :
    norm k (1 : k' ≃ₐ[k] k') g = g ^ Module.finrank k k' := by
  simp [norm, one_pow, galAct_one, List.prod_ofFn, Finset.prod_const]

end GlobalTheory.LBC

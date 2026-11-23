import Mathlib
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsLinearMapMultilinearMapBaseChange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsFrameOfBijectiveStalk

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.QCoh GlobalTheory.Twist GlobalTheory.CechPic

namespace GlobalTheory.Vert

section Length

variable {R : Type*} [CommRing R]

theorem length_eq_range_add_range {A B C : Type*} [AddCommGroup A] [AddCommGroup B]
    [AddCommGroup C] [Module R A] [Module R B] [Module R C] {f : A →ₗ[R] B} {g : B →ₗ[R] C}
    (h : Function.Exact f g) :
    Module.length R B = Module.length R (LinearMap.range f) + Module.length R (LinearMap.range g) :=
  Module.length_eq_add_of_exact (LinearMap.range f).subtype g.rangeRestrict
    (Submodule.subtype_injective _) g.surjective_rangeRestrict fun x => by
      rw [← LinearMap.mem_ker, LinearMap.ker_rangeRestrict, h.linearMap_ker_eq, Set.mem_range]
      exact ⟨fun hx => ⟨⟨x, hx⟩, rfl⟩, fun ⟨y, hy⟩ => hy ▸ y.2⟩

theorem toNat_length_eq_range_add_range {A B C : Type*} [AddCommGroup A] [AddCommGroup B]
    [AddCommGroup C] [Module R A] [Module R B] [Module R C] {f : A →ₗ[R] B} {g : B →ₗ[R] C}
    (h : Function.Exact f g) (hB : Module.length R B ≠ ⊤) :
    ((Module.length R B).toNat : ℤ) = (Module.length R (LinearMap.range f)).toNat +
      (Module.length R (LinearMap.range g)).toNat := by
  rw [length_eq_range_add_range h] at hB ⊢
  rw [ENat.toNat_add (WithTop.add_ne_top.1 hB).1 (WithTop.add_ne_top.1 hB).2, Nat.cast_add]

theorem length_ne_top_of_exact {A B C : Type*} [AddCommGroup A] [AddCommGroup B]
    [AddCommGroup C] [Module R A] [Module R B] [Module R C] {f : A →ₗ[R] B} {g : B →ₗ[R] C}
    (h : Function.Exact f g) (hA : Module.length R A ≠ ⊤) (hC : Module.length R C ≠ ⊤) :
    Module.length R B ≠ ⊤ := by
  rw [length_eq_range_add_range h]
  exact WithTop.add_ne_top.2
    ⟨ne_top_of_le_ne_top hA (Module.length_le_of_surjective _ f.surjective_rangeRestrict),
      ne_top_of_le_ne_top hC (Module.length_le_of_injective _ (Submodule.subtype_injective _))⟩

end Length

section Chi

variable {X Y : Scheme.{0}} (R : Type) [CommRing R] [Algebra R Γ(X, ⊤)]

structure FiniteLenCoh (F : X.Modules) : Prop where

  ne_top : ∀ n, Module.length R (coh F n) ≠ ⊤

  eventually_zero : ∃ N, ∀ n, N ≤ n → Subsingleton (coh F n)

def chiLen (F : X.Modules) : ℤ := ∑ᶠ n, (-1 : ℤ) ^ n * (Module.length R (coh F n)).toNat

variable {F G : X.Modules} {S : ShortComplex X.Modules}

theorem chiLen_eq_sum_range (N : ℕ) (hN : ∀ n, N ≤ n → Subsingleton (coh F n)) :
    chiLen R F = ∑ n ∈ Finset.range N, (-1 : ℤ) ^ n * (Module.length R (coh F n)).toNat :=
  finsum_eq_sum_of_support_subset _ fun n hn => by
    by_contra h
    have := hN n (by simpa using h)
    exact hn (by simp [Module.length_eq_zero])

theorem chiLen_eq_of_linearEquiv [Algebra R Γ(Y, ⊤)] {H : Y.Modules}
    (e : ∀ n, coh F n ≃ₗ[R] coh H n) : chiLen R F = chiLen R H :=
  finsum_congr fun n => by rw [(e n).length_eq]

theorem chiLen_congr (e : F ≅ G) : chiLen R F = chiLen R G :=
  chiLen_eq_of_linearEquiv R fun n => cohOn.mapIso R ⊤ n e

theorem chiLen_eq_zero_of_isZero (h : IsZero F) : chiLen R F = 0 := by
  rw [chiLen_eq_sum_range R 0 fun n _ => cohOn.subsingleton_of_isZero h ⊤ n]; simp

theorem chiLen_eq_chi (k : Type) [Field k] [Algebra k Γ(X, ⊤)] (F : X.Modules) :
    chiLen k F = chi k F :=
  finsum_congr fun n => by
    rw [hdim_def, Module.length_eq_rank, Cardinal.toNat_toENat]; rfl

theorem chiLen_eq_of_surjective (k : Type) [CommRing k] [Algebra R k] [Algebra k Γ(X, ⊤)]
    [IsScalarTower R k Γ(X, ⊤)] (h : Function.Surjective (algebraMap R k)) (F : X.Modules) :
    chiLen R F = chiLen k F :=
  finsum_congr fun n => by rw [Module.length_eq_of_surjective (M := coh F n) h]

variable {R}

namespace FiniteLenCoh

theorem of_iso (h : FiniteLenCoh R F) (e : F ≅ G) : FiniteLenCoh R G where
  ne_top n := (cohOn.mapIso R ⊤ n e).length_eq ▸ h.ne_top n
  eventually_zero :=
    have ⟨N, hN⟩ := h.eventually_zero
    ⟨N, fun n hn => have := hN n hn; (cohOn.mapIso R ⊤ n e).symm.injective.subsingleton⟩

theorem of_shortExact₂ (hS : S.ShortExact) (h₁ : FiniteLenCoh R S.X₁) (h₃ : FiniteLenCoh R S.X₃) :
    FiniteLenCoh R S.X₂ where
  ne_top n := length_ne_top_of_exact (cohOn.exact₂ R hS ⊤ n) (h₁.ne_top n) (h₃.ne_top n)
  eventually_zero :=
    have ⟨N₁, h₁⟩ := h₁.eventually_zero
    have ⟨N₃, h₃⟩ := h₃.eventually_zero
    ⟨max N₁ N₃, fun n hn => cohOn.subsingleton₂ hS ⊤ n (h₁ n (by omega)) (h₃ n (by omega))⟩

theorem of_shortExact₃ (hS : S.ShortExact) (h₁ : FiniteLenCoh R S.X₁) (h₂ : FiniteLenCoh R S.X₂) :
    FiniteLenCoh R S.X₃ where
  ne_top n := length_ne_top_of_exact (cohOn.exact₃ R hS ⊤ n) (h₂.ne_top n) (h₁.ne_top (n + 1))
  eventually_zero :=
    have ⟨N₁, h₁⟩ := h₁.eventually_zero
    have ⟨N₂, h₂⟩ := h₂.eventually_zero
    ⟨max N₁ N₂, fun n hn => cohOn.subsingleton₃ hS ⊤ n (h₂ n (by omega)) (h₁ (n + 1) (by omega))⟩

end FiniteLenCoh

theorem chiLen_shortExact (hS : S.ShortExact) (h₁ : FiniteLenCoh R S.X₁)
    (h₃ : FiniteLenCoh R S.X₃) : chiLen R S.X₂ = chiLen R S.X₁ + chiLen R S.X₃ := by
  have h₂ := h₁.of_shortExact₂ hS h₃
  obtain ⟨N₁, hN₁⟩ := h₁.eventually_zero
  obtain ⟨N₂, hN₂⟩ := h₂.eventually_zero
  obtain ⟨N₃, hN₃⟩ := h₃.eventually_zero
  let a : ℕ → ℤ := fun n => (Module.length R (LinearMap.ker (cohOn.map R S.f ⊤ n))).toNat
  have key (N : ℕ) : ∑ n ∈ Finset.range N, (-1 : ℤ) ^ n * (Module.length R (coh S.X₁ n)).toNat +
      ∑ n ∈ Finset.range N, (-1 : ℤ) ^ n * (Module.length R (coh S.X₃ n)).toNat =
      ∑ n ∈ Finset.range N, (-1 : ℤ) ^ n * (Module.length R (coh S.X₂ n)).toNat +
        (a 0 - (-1) ^ N * a N) := by
    induction N with
    | zero => simp
    | succ N ih =>
      have e₁ := toNat_length_eq_range_add_range (LinearMap.exact_subtype_ker_map
        (cohOn.map R S.f ⊤ N)) (h₁.ne_top N)
      have e₂ := toNat_length_eq_range_add_range (cohOn.exact₂ R hS ⊤ N) (h₂.ne_top N)
      have e₃ := toNat_length_eq_range_add_range (cohOn.exact₃ R hS ⊤ N) (h₃.ne_top N)
      rw [Submodule.range_subtype] at e₁
      rw [← (cohOn.exact₁ R hS ⊤ N).linearMap_ker_eq] at e₃
      simp only [Finset.sum_range_succ, pow_succ]
      change _ = a N + _ at e₁
      change _ = _ + a (N + 1) at e₃
      erw [e₁, e₂, e₃]
      linear_combination ih
  have a0 : a 0 = 0 := by
    simp only [a]
    rw [LinearMap.ker_eq_bot.2 (cohOn.injective_zero R hS ⊤)]
    simp
  let N := max N₁ (max N₂ N₃)
  have aN : a N = 0 := by
    have := hN₁ N (by omega)
    simp [a, Module.length_eq_zero]
  rw [chiLen_eq_sum_range R N fun n hn => hN₁ n (by omega),
    chiLen_eq_sum_range R N fun n hn => hN₂ n (by omega),
    chiLen_eq_sum_range R N fun n hn => hN₃ n (by omega), key, a0, aN]
  simp

end Chi

section Twists

variable {X Y : Scheme.{0}} (R : Type) [CommRing R] [Algebra R Γ(X, ⊤)]

def FiniteLenTwists (F : X.Modules) : Prop := ∀ M : LB X, M.IsLB → FiniteLenCoh R (twist F M)

def chiLenPic (F : X.Modules) : Pic X → ℤ :=
  Quotient.lift (fun M => chiLen R (twist F M.1)) fun M N h =>
    (Twist.nonempty_iso_of_lbIso M.2 N.2 h).elim (chiLen_congr R)

def interLen {ι : Type} [Fintype ι] (F : X.Modules) (L : ι → LB X) : ℤ :=
  ∑ S : Finset ι, (-1 : ℤ) ^ S.card * chiLen R (twist F (lbInvProd L S))

variable {F G : X.Modules} {M N : LB X} {S : ShortComplex X.Modules}

variable (F) in

@[simp] theorem chiLenPic_cls (hM : M.IsLB) : chiLenPic R F (cls M hM) = chiLen R (twist F M) := rfl

theorem chiLenPic_congr (e : F ≅ G) : chiLenPic R F = chiLenPic R G := by
  funext c
  obtain ⟨M, hM, rfl⟩ := cls_surj c
  exact chiLen_congr R ((twistFunctor M).mapIso e)

variable (F) in

theorem chiLenPic_twist (hM : M.IsLB) (c : Pic X) :
    chiLenPic R (twist F M) c = chiLenPic R F (cls M hM + c) := by
  obtain ⟨N, hN, rfl⟩ := cls_surj c
  exact (nonempty_twist_twist_iso_of_cls_eq F hM hN (isLB_tens hM hN) rfl).elim (chiLen_congr R)

theorem chiLenPic_eq_zero_of_isZero (h : IsZero F) : chiLenPic R F = 0 := by
  funext c
  obtain ⟨M, hM, rfl⟩ := cls_surj c
  exact chiLen_eq_zero_of_isZero R ((isZero_twist_iff hM).2 h)

variable (F) in

theorem interLen_eq_multiDiff {ι : Type} [Fintype ι] {L : ι → LB X} (hL : ∀ i, (L i).IsLB) :
    interLen R F L = multiDiff (fun i => cls (L i) (hL i)) (chiLenPic R F) 0 :=
  Finset.sum_congr rfl fun S _ => by
    rw [zero_sub, ← cls_lbInvProd hL S (isLB_lbInvProd hL S), chiLenPic_cls, smul_eq_mul]

theorem chiLenPic_pushforward (k : Type) [Field k] [Algebra R k] [Algebra k Γ(Y, ⊤)]
    (hk : Function.Surjective (algebraMap R k)) (i : Y ⟶ X) [IsClosedImmersion i]
    (hi : ∀ r : R, i.appTop (algebraMap R Γ(X, ⊤) r) = algebraMap k Γ(Y, ⊤) (algebraMap R k r))
    (H : Y.Modules) :
    chiLenPic R ((Scheme.Modules.pushforward i).obj H) = chiPic k H ∘ pull i := by
  funext c
  obtain ⟨M, hM, rfl⟩ := cls_surj c
  letI : Algebra R Γ(Y, ⊤) := ((algebraMap k Γ(Y, ⊤)).comp (algebraMap R k)).toAlgebra
  have : IsScalarTower R k Γ(Y, ⊤) := .of_algebraMap_eq fun _ => rfl
  refine (chiLen_congr R (Twist.projIso M i H)).symm.trans ?_
  rw [chiLen_eq_of_linearEquiv R fun n => LinearEquiv.ofBijective _
    (cohPushMap_bijective_of_isClosedImmersion R i hi _ ⊤ n), chiLen_eq_of_surjective R k hk,
    chiLen_eq_chi]
  rfl

variable {R}

theorem FiniteLenTwists.of_iso (h : FiniteLenTwists R F) (e : F ≅ G) : FiniteLenTwists R G :=
  fun M hM => (h M hM).of_iso ((twistFunctor M).mapIso e)

theorem FiniteLenTwists.twist (h : FiniteLenTwists R F) (hM : M.IsLB) :
    FiniteLenTwists R (twist F M) :=
  fun N hN => (nonempty_twist_twist_iso_of_cls_eq F hM hN (isLB_tens hM hN) rfl).elim
    fun e => (h _ (isLB_tens hM hN)).of_iso e.symm

theorem FiniteLenTwists.of_shortExact₃ (hS : S.ShortExact) (h₁ : FiniteLenTwists R S.X₁)
    (h₂ : FiniteLenTwists R S.X₂) : FiniteLenTwists R S.X₃ :=
  fun M hM => FiniteLenCoh.of_shortExact₃ (Twist.shortExact_map hM hS) (h₁ M hM) (h₂ M hM)

theorem chiLenPic_shortExact (hS : S.ShortExact) (h₁ : FiniteLenTwists R S.X₁)
    (h₃ : FiniteLenTwists R S.X₃) :
    chiLenPic R S.X₂ = chiLenPic R S.X₁ + chiLenPic R S.X₃ := by
  funext c
  obtain ⟨M, hM, rfl⟩ := cls_surj c
  have := chiLen_shortExact (Twist.shortExact_map hM hS) (h₁ M hM) (h₃ M hM)
  exact this

theorem bwdDiff_chiLenPic {L : LB X} (hL : L.IsLB) (s : L.Sec) [Mono (cutHom F hL s)]
    (h : FiniteLenTwists R F) : FiniteLenTwists R (cut F hL s) ∧
      bwdDiff (cls L hL) (chiLenPic R F) = chiLenPic R (cut F hL s) := by
  have h₁ := h.twist (isLB_lbZPow hL (-1))
  have h₃ := h₁.of_shortExact₃ (shortExact_cutComplex F hL s) h
  refine ⟨h₃, funext fun c => ?_⟩
  have e := congrFun (chiLenPic_shortExact (shortExact_cutComplex F hL s) h₁ h₃) c
  change chiLenPic R F c =
    chiLenPic R (twist F (lbZPow L (-1))) c + chiLenPic R (cut F hL s) c at e
  rw [chiLenPic_twist R F (isLB_lbZPow hL (-1)), cls_lbZPow hL, neg_one_zsmul,
    neg_add_eq_sub] at e
  rw [bwdDiff_apply, e, add_sub_cancel_left]

theorem diffVanish_chiLenPic [IsLocallyNoetherian X] {A : LB X} (hA : IsAmpleLB A)
    [IsFiniteQC F] (h : FiniteLenTwists R F) {n : ℕ} (hn : suppDim F < n) :
    DiffVanish n (chiLenPic R F) := by
  induction n generalizing F with
  | zero => exact diffVanish_zero_iff.2 (chiLenPic_eq_zero_of_isZero R (suppDim_lt_zero_iff.1 hn))
  | succ n ih =>
    refine diffVanish_of_generators
      (S := {c | ∃ (L : LB X) (hL : L.IsLB) (s : L.Sec), Mono (cutHom F hL s) ∧ c = cls L hL})
      (eq_top_iff.2 fun c _ => ?_) fun g hg => ?_
    · obtain ⟨P, Q, hP, hQ, s, t, hs, ht, rfl⟩ := hA.exists_sub_of_mono_cutHom F c
      exact sub_mem (AddSubgroup.subset_closure ⟨P, hP, s, hs, rfl⟩)
        (AddSubgroup.subset_closure ⟨Q, hQ, t, ht, rfl⟩)
    · obtain ⟨L, hL, s, hs, e⟩ := hg 0
      rw [← Fin.cons_self_tail g, multiDiff_cons', e, (bwdDiff_chiLenPic hL s h).2]
      refine ih (bwdDiff_chiLenPic hL s h).1 ?_ _
      have := (suppDim_cut_add_one_le F hL s).trans_lt hn
      by_contra hc
      rw [not_lt] at hc
      refine this.not_ge ?_
      push_cast
      exact add_le_add_left hc 1

theorem exists_smulHom_pow_eq_zero [CompactSpace X] [IsFiniteQC F] (a : Γ(X, ⊤))
    (h : ∀ x ∈ support F, x ∉ X.basicOpen a) : ∃ m : ℕ, smulHom F (a ^ m) = 0 := by
  let i := (annihilatorSheaf F).subschemeι
  have : CompactSpace (annihilatorSheaf F).subscheme :=
    QuasiCompact.compactSpace_of_compactSpace i
  have hb : (annihilatorSheaf F).subscheme.basicOpen (i.appTop a) = ⊥ := by
    refine (Scheme.preimage_basicOpen i a).symm.trans (eq_bot_iff.2 fun y hy => ?_)
    exact h _ (range_annihilatorSheaf_subschemeι F ▸ ⟨y, rfl⟩) hy
  obtain ⟨m, hm⟩ := (Scheme.isNilpotent_iff_basicOpen_eq_bot _).2 hb
  refine ⟨m, ?_⟩
  have e := pushforward_map_smulHom i (onAnnihilator F) (a ^ m)
  rw [map_pow, hm, smulHom_zero, Functor.map_zero] at e
  rw [← cancel_mono (isoPushforwardOnAnnihilator F).hom, smulHom_comp, zero_comp]
  exact (congrArg _ e.symm).trans comp_zero

theorem finiteLenTwists_of_support [IsDomain R] [IsNoetherianRing R] [Ring.KrullDimLE 1 R]
    {f : X ⟶ Sp R} (hf : ∀ r, algebraMap R Γ(X, ⊤) r = f.appTop ((Scheme.ΓSpecIso (.of R)).inv r))
    (hp : IsProjOver f) [IsFiniteQC F] {n : ℕ} (hn : suppDim F < n) {a : R} (ha : a ≠ 0)
    (h : ∀ x ∈ support F, x ∉ X.basicOpen (algebraMap R Γ(X, ⊤) a)) : FiniteLenTwists R F := by
  intro M hM
  have := isNoetherian_of_isProjOver hp
  have := isFiniteQC_twist (F := F) hM
  refine ⟨fun i => ?_, n, fun i hi => subsingleton_coh_of_isProjOver hp _
    (((suppDim_twist hM).trans_lt hn).trans_le (by exact_mod_cast hi))⟩
  have := finite_coh_of_isProjOver hf (twist F M) hp i
  obtain ⟨m, hm⟩ := exists_smulHom_pow_eq_zero (F := twist F M) _ (by rwa [support_twist hM])
  have hk : a ^ m ∈ Module.annihilator R (coh (twist F M) i) :=
    Module.mem_annihilator.2 fun x => (cohOn.toH' _ _ _).injective (by
      rw [cohOn.toH'_smul, map_pow, hm, Functor.map_zero, map_zero, SiteCoh.map_zero_apply])
  have := isFiniteLength_iff_isNoetherian_isArtinian.1
    (isFiniteLength_quotient_span_singleton R (mem_nonZeroDivisors_of_ne_zero (pow_ne_zero m ha)))
  have : IsArtinian R (R ⧸ Module.annihilator R (coh (twist F M) i)) :=
    have := this.2
    isArtinian_of_surjective _ (Submodule.factor ((Ideal.span_singleton_le_iff_mem _).2 hk))
      (Submodule.factor_surjective _)
  have : IsArtinianRing (R ⧸ Module.annihilator R (coh (twist F M) i)) := isArtinian_of_tower R this
  exact Module.length_ne_top_iff.2 isFiniteLength_of_isArtinianRing_annihilator

end Twists

section Sym

variable {G H : Type*} [AddCommGroup G] [AddCommGroup H]

variable (G) in

abbrev SymQ : Type _ := SymmetricAlgebra ℚ (ℚ ⊗[ℤ] G)

def symOf : G →+ SymQ G :=
  (SymmetricAlgebra.ι ℚ _).toAddMonoidHom.comp (TensorProduct.mk ℤ ℚ G 1).toAddMonoidHom

theorem symOf_apply (g : G) : symOf g = SymmetricAlgebra.ι ℚ _ ((1 : ℚ) ⊗ₜ[ℤ] g) := rfl

def symLift {A : Type*} [CommRing A] [Algebra ℚ A] (f : G →+ A) : SymQ G →ₐ[ℚ] A :=
  SymmetricAlgebra.lift (LinearMap.liftBaseChange ℚ f.toIntLinearMap)

@[simp] theorem symLift_symOf {A : Type*} [CommRing A] [Algebra ℚ A] (f : G →+ A) (g : G) :
    symLift f (symOf g) = f g := by
  simp [symLift, symOf_apply]

def symMap (f : G →+ H) : SymQ G →ₐ[ℚ] SymQ H := symLift (symOf.comp f)

@[simp] theorem symMap_symOf (f : G →+ H) (g : G) : symMap f (symOf g) = symOf (f g) :=
  symLift_symOf _ g

variable (G) in

def symDeg (n : ℕ) : Submodule ℚ (SymQ G) :=
  Submodule.span ℚ (Set.range fun g : Fin n → G => ∏ i, symOf (g i))

theorem span_prod_symOf : Submodule.span ℚ
    (Set.range fun s : Multiset G => (s.map symOf).prod) = (⊤ : Submodule ℚ (SymQ G)) := by
  refine eq_top_iff.2 fun x hx => ?_
  clear hx
  induction x using SymmetricAlgebra.induction with
  | algebraMap r =>
    rw [Algebra.algebraMap_eq_smul_one]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨0, by simp⟩)
  | ι x =>
    induction x with
    | zero => rw [map_zero]; exact zero_mem _
    | tmul a g =>
      rw [← mul_one a, ← smul_eq_mul, ← smul_tmul', map_smul]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨{g}, by simp [symOf_apply]⟩)
    | add a b ha hb => rw [map_add]; exact add_mem ha hb
  | mul a b ha hb =>
    have := Submodule.mul_mem_mul ha hb
    rw [Submodule.span_mul_span] at this
    refine Submodule.span_mono ?_ this
    rintro _ ⟨_, ⟨s, rfl⟩, _, ⟨t, rfl⟩, rfl⟩
    exact ⟨s + t, by simp⟩
  | add a b ha hb => exact add_mem ha hb

theorem symQ_linearMap_ext {N : Type*} [AddCommGroup N] [Module ℚ N] {l l' : SymQ G →ₗ[ℚ] N}
    (h : ∀ (n : ℕ) (g : Fin n → G), l (∏ i, symOf (g i)) = l' (∏ i, symOf (g i))) : l = l' := by
  refine LinearMap.ext_on_range span_prod_symOf fun s => ?_
  induction s using Quotient.inductionOn with
  | h s =>
    have := h s.length s.get
    rwa [← List.prod_ofFn, ← Function.comp_def, ← List.map_ofFn, List.ofFn_get] at this

variable {φ ψ : G → ℤ} {d : ℕ}

theorem exists_topForm (h : DiffVanish (d + 1) φ) : ∃ l : SymQ G →ₗ[ℚ] ℚ,
    ∀ (ι : Type) [Fintype ι] (g : ι → G),
      l (∏ i, symOf (g i)) = if Fintype.card ι = d then ((multiDiff g φ 0 : ℤ) : ℚ) else 0 := by
  classical
  let f : Multiset G → ℚ := fun s =>
    if s.card = d then (shiftAct G ℤ (s.map diffElt).prod φ 0 : ℚ) else 0
  have hf (a b : G) (s : Multiset G) : f (s + {a + b}) = f (s + {a}) + f (s + {b}) := by
    simp only [f, Multiset.card_add, Multiset.card_singleton, Multiset.map_add,
      Multiset.map_singleton, Multiset.prod_add, Multiset.prod_singleton]
    split_ifs with hs
    · have : (s.map diffElt).prod * (diffElt a * diffElt b) ∈ diffIdeal G ^ (d + 1) := by
        rw [← hs, add_assoc, pow_add, pow_add, pow_one]
        refine Ideal.mul_mem_mul ?_ (Ideal.mul_mem_mul (diffElt_mem a) (diffElt_mem b))
        induction s using Quotient.inductionOn with
        | h s =>
          have := prod_diffElt_mem Finset.univ s.get
          rw [← List.prod_ofFn, ← Function.comp_def, ← List.map_ofFn, List.ofFn_get] at this
          simpa using this
      rw [diffElt_add, mul_sub, mul_add, map_sub, map_add, LinearMap.sub_apply,
        h.shiftAct_eq_zero this]
      simp
    · simp
  let l : MvPolynomial G ℚ →ₗ[ℚ] ℚ :=
    (MvPolynomial.basisMonomials G ℚ).constr ℚ fun m => f (Finsupp.toMultiset m)
  have hl (m : G →₀ ℕ) : l (MvPolynomial.monomial m 1) = f (Finsupp.toMultiset m) :=
    (MvPolynomial.basisMonomials G ℚ).constr_basis ℚ _ m
  let J : Ideal (MvPolynomial G ℚ) := Ideal.span (Set.range fun p : G × G =>
    MvPolynomial.X (p.1 + p.2) - (MvPolynomial.X p.1 + MvPolynomial.X p.2))
  have hJ : J.restrictScalars ℚ ≤ LinearMap.ker l := by
    intro x hx
    suffices ∀ r, l (r * x) = 0 by simpa using this 1
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨p, rfl⟩ := hx
      intro r
      induction r using MvPolynomial.induction_on' with
      | monomial m c =>
        rw [show MvPolynomial.monomial m c = c • MvPolynomial.monomial m (1 : ℚ) by
          simp [MvPolynomial.smul_monomial], smul_mul_assoc, map_smul]
        simp only [mul_sub, mul_add, map_sub, map_add, MvPolynomial.X,
          MvPolynomial.monomial_mul, mul_one, hl, Finsupp.toMultiset_single, one_nsmul, hf]
        simp
      | add p q hp hq => rw [add_mul, map_add, hp, hq, add_zero]
    | zero => simp
    | add x y _ _ hx hy => intro r; rw [mul_add, map_add, hx, hy, add_zero]
    | smul a x _ hx => intro r; rw [smul_eq_mul, ← mul_assoc, hx]
  let c : G →+ MvPolynomial G ℚ ⧸ J := AddMonoidHom.mk' (fun g => Ideal.Quotient.mk J (.X g))
    fun a b => by
      rw [← map_add, Ideal.Quotient.eq]
      exact Ideal.subset_span ⟨(a, b), rfl⟩
  refine ⟨(J.restrictScalars ℚ).liftQ l hJ ∘ₗ
    (Submodule.Quotient.restrictScalarsEquiv ℚ J).symm.toLinearMap ∘ₗ (symLift c).toLinearMap,
    fun ι _ g => ?_⟩
  have e : symLift c (∏ i, symOf (g i)) =
      Ideal.Quotient.mk J (MvPolynomial.monomial (∑ i, Finsupp.single (g i) 1) 1) := by
    rw [MvPolynomial.monomial_sum_one, map_prod, map_prod]
    exact Finset.prod_congr rfl fun i _ => symLift_symOf c _
  refine (congrArg (fun x => (J.restrictScalars ℚ).liftQ l hJ
    ((Submodule.Quotient.restrictScalarsEquiv ℚ J).symm x)) e).trans ((hl _).trans ?_)
  have e' : Finsupp.toMultiset (∑ i, Finsupp.single (g i) 1) = Finset.univ.val.map g := by
    simp only [map_sum, Finsupp.toMultiset_single, one_nsmul]
    rw [Finset.sum_eq_multiset_sum, ← Multiset.sum_map_singleton (Finset.univ.val.map g),
      Multiset.map_map]
    rfl
  simp only [f, e', Multiset.card_map, Multiset.map_map, multiDiff_eq_shiftAct]
  rfl

def topForm (h : DiffVanish (d + 1) φ) : SymQ G →ₗ[ℚ] ℚ := (exists_topForm h).choose

theorem topForm_prod (h : DiffVanish (d + 1) φ) {ι : Type} [Fintype ι] (g : ι → G) :
    topForm h (∏ i, symOf (g i)) = if Fintype.card ι = d then ((multiDiff g φ 0 : ℤ) : ℚ) else 0 :=
  (exists_topForm h).choose_spec ι g

theorem topForm_eq_zero (h : DiffVanish (d + 1) φ) {n : ℕ} (hn : n ≠ d) {x : SymQ G}
    (hx : x ∈ symDeg G n) : topForm h x = 0 := by
  refine (Submodule.span_le (p := LinearMap.ker (topForm h))).2 ?_ hx
  rintro _ ⟨g, rfl⟩
  exact (topForm_prod h g).trans (if_neg (by simpa using hn))

theorem topForm_eq_add {χ : G → ℤ} (h : DiffVanish (d + 1) χ) (h₁ : DiffVanish (d + 1) φ)
    (h₂ : DiffVanish (d + 1) ψ) (a : G) (e : ∀ x, χ x = φ (a + x) + ψ x) :
    topForm h = topForm h₁ + topForm h₂ := by
  refine symQ_linearMap_ext fun n g => ?_
  simp only [LinearMap.add_apply, topForm_prod]
  split_ifs with hn
  · rw [show χ = (fun x => φ (a + x)) + ψ from funext e, multiDiff_add, Pi.add_apply,
      multiDiff_translate, h₁.multiDiff_eq_of_le_card hn.ge g _ 0, Int.cast_add]
  · simp

example : topForm (diffVanish_pow_int 2).1 (∏ _i : Fin 2, symOf 1) = 2 ∧
    topForm (diffVanish_pow_int 2).1 (∏ _i : Fin 1, symOf 1) = 0 := by
  rw [topForm_prod, topForm_prod, multiDiff_pow]
  simp

end Sym

section SmallPic

variable {X Y Z : Scheme.{0}}

instance small_pic : Small.{0} (Pic X) := by
  refine small_of_surjective (α := {p : Σ U : X → X.Opens, ∀ i j, Γ(X, U i ⊓ U j)ˣ //
    LB.IsLB ⟨X, p.1, p.2⟩}) (f := fun p => cls _ p.2) fun c => ?_
  obtain ⟨L, hL, rfl⟩ := cls_surj c
  choose j hj using LB.mem_of_cover hL
  have h : LB.IsLB ⟨X, fun x => L.U (j x), fun x y => L.g (j x) (j y)⟩ :=
    ⟨top_le_iff.1 fun x _ => Opens.mem_iSup.2 ⟨x, hj x⟩, fun _ => hL.g_self _,
      fun _ _ _ => hL.cocycle _ _ _⟩
  exact ⟨⟨⟨_, _⟩, h⟩, (cls_eq_iff h hL).2
    (iso_of_chart hL ⟨j, fun _ => le_rfl, fun _ _ _ _ _ => rfl⟩)⟩

variable (X) in

abbrev SmallPic : Type := Shrink.{0} (Pic X)

variable (X) in

def smallPicEquiv : SmallPic X ≃+ Pic X := Shrink.addEquiv

def smallCls (L : LB X) (hL : L.IsLB) : SmallPic X := (smallPicEquiv X).symm (cls L hL)

@[simp] theorem smallPicEquiv_smallCls (L : LB X) (hL : L.IsLB) :
    smallPicEquiv X (smallCls L hL) = cls L hL := (smallPicEquiv X).apply_symm_apply _

theorem smallCls_surj (c : SmallPic X) : ∃ L hL, smallCls L hL = c :=
  have ⟨L, hL, e⟩ := cls_surj (smallPicEquiv X c)
  ⟨L, hL, (smallPicEquiv X).symm_apply_eq.2 e⟩

theorem smallCls_eq_iff {L M : LB X} (hL : L.IsLB) (hM : M.IsLB) :
    smallCls L hL = smallCls M hM ↔ LBIso L M :=
  (smallPicEquiv X).symm.injective.eq_iff.trans (cls_eq_iff hL hM)

def smallPull (f : Y ⟶ X) : SmallPic X →+ SmallPic Y :=
  (smallPicEquiv Y).symm.toAddMonoidHom.comp ((pull f).comp (smallPicEquiv X).toAddMonoidHom)

theorem smallPull_smallCls (f : Y ⟶ X) {L : LB X} (hL : L.IsLB) (h : (L.pull f).IsLB) :
    smallPull f (smallCls L hL) = smallCls (L.pull f) h := by
  simp [smallPull, smallCls, cls_pull hL]

variable (X) in

abbrev PicSym : Type := SymQ (SmallPic X)

def c1 (L : LB X) (hL : L.IsLB) : PicSym X := symOf (smallCls L hL)

def firstChernPic : Pic X →+ PicSym X := symOf.comp (smallPicEquiv X).symm.toAddMonoidHom

@[simp] theorem firstChernPic_class (L : LB X) (hL : L.IsLB) : firstChernPic (cls L hL) = c1 L hL := rfl

theorem firstChernTensor {L M : LB X} (hL : L.IsLB) (hM : M.IsLB) (h : (tens L M).IsLB) :
    c1 (tens L M) h = c1 L hL + c1 M hM := map_add firstChernPic (cls L hL) (cls M hM)

theorem firstChern_trivial (h : (LB.triv X).IsLB) : c1 (LB.triv X) h = 0 := map_zero firstChernPic

theorem firstChernCongr {L M : LB X} (hL : L.IsLB) (hM : M.IsLB) (h : LBIso L M) : c1 L hL = c1 M hM :=
  congrArg symOf ((smallCls_eq_iff hL hM).2 h)

def picSymPull (f : Y ⟶ X) : PicSym X →ₐ[ℚ] PicSym Y := symMap (smallPull f)

theorem pullback_firstChern (f : Y ⟶ X) {L : LB X} (hL : L.IsLB) (h : (L.pull f).IsLB) :
    picSymPull f (c1 L hL) = c1 (L.pull f) h :=
  (symMap_symOf _ _).trans (congrArg symOf (smallPull_smallCls f hL h))

theorem picSymPull_c1Pic (f : Y ⟶ X) (c : Pic X) :
    picSymPull f (firstChernPic c) = firstChernPic (pull f c) := by
  obtain ⟨L, hL, rfl⟩ := cls_surj c
  exact pullback_firstChern f hL _

variable {d : ℕ} {φ ψ : Pic X → ℤ}

def picForm (h : DiffVanish (d + 1) φ) : PicSym X →ₗ[ℚ] ℚ :=
  topForm (h.comap (smallPicEquiv X).toAddMonoidHom)

theorem picForm_prod (h : DiffVanish (d + 1) φ) {ι : Type} [Fintype ι] (g : ι → Pic X) :
    picForm h (∏ i, firstChernPic (g i)) = if Fintype.card ι = d then ((multiDiff g φ 0 : ℤ) : ℚ) else 0 := by
  refine (topForm_prod _ fun i => (smallPicEquiv X).symm (g i)).trans ?_
  rw [multiDiff_comap]
  simp [Function.comp_def]

theorem picSym_linearMap_ext {N : Type*} [AddCommGroup N] [Module ℚ N] {l l' : PicSym X →ₗ[ℚ] N}
    (h : ∀ (n : ℕ) (g : Fin n → Pic X), l (∏ i, firstChernPic (g i)) = l' (∏ i, firstChernPic (g i))) : l = l' :=
  symQ_linearMap_ext fun n g => by simpa [firstChernPic] using h n fun i => smallPicEquiv X (g i)

theorem picForm_eq_add {χ : Pic X → ℤ} (h : DiffVanish (d + 1) χ) (h₁ : DiffVanish (d + 1) φ)
    (h₂ : DiffVanish (d + 1) ψ) (a : Pic X) (e : ∀ x, χ x = φ (a + x) + ψ x) :
    picForm h = picForm h₁ + picForm h₂ :=
  topForm_eq_add _ _ _ ((smallPicEquiv X).symm a) fun x => by simpa using e _

theorem picForm_comap (f : Y ⟶ X) {χ : Pic Y → ℤ} (h : DiffVanish (d + 1) χ) (x : PicSym X) :
    picForm (h.comap (pull f)) x = picForm h (picSymPull f x) := by
  refine LinearMap.congr_fun (picSym_linearMap_ext
    (l' := picForm h ∘ₗ (picSymPull f).toLinearMap) fun n g => ?_) x
  simp only [LinearMap.comp_apply, AlgHom.toLinearMap_apply, map_prod, picSymPull_c1Pic,
    picForm_prod]
  rw [multiDiff_comap, Function.comp_apply, map_zero]
  rfl

theorem picForm_eq_zero (h : DiffVanish (d + 1) φ) {n : ℕ} (hn : n ≠ d) {x : PicSym X}
    (hx : x ∈ symDeg (SmallPic X) n) : picForm h x = 0 := topForm_eq_zero _ hn hx

end SmallPic

end GlobalTheory.Vert

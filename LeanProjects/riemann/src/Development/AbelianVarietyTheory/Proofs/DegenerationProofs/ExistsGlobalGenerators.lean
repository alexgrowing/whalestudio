import Mathlib
import Development.AbelianVarietyTheory.Definitions.Degenerations.ArithBase
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsMulPowMemOOfIsAffineOpen
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.SpanEqSpanMinor

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open Matrix

noncomputable section
namespace GlobalTheory.ZH.GlobalGen

theorem sum_eq_zero_of_mul {A o : Type} [AddGroup A] [Fintype A] [CommRing o] [IsDomain o] (ψ : A → o)
    (h : ∀ a b, ψ (a + b) = ψ a * ψ b) {a : A} (ha : ψ a ≠ 1) : ∑ b, ψ b = 0 := by
  have e : ∑ b, ψ (a + b) = ∑ b, ψ b := Equiv.sum_comp (Equiv.addLeft a) ψ
  simp only [h, ← Finset.mul_sum] at e
  by_contra h0
  exact ha (mul_right_cancel₀ h0 (e.trans (_root_.one_mul _).symm))

section Proj

variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] (S : ThetaSys o Ω)

theorem N_pos : 0 < S.N := lt_of_lt_of_le two_pos S.N_ge

instance neZero_N : NeZero S.N := ⟨(N_pos S).ne'⟩

instance neZero_rN : NeZero (S.r * S.N) := ⟨(Nat.mul_pos S.r_pos (N_pos S)).ne'⟩

theorem isPrimitiveRoot_ζN : IsPrimitiveRoot S.ζN S.N :=
  S.prim.pow (pow_pos (Nat.mul_pos S.r_pos (N_pos S)) 2) (by ring)

def chi (a : ZMod S.N) : o := S.ζN ^ (-a).val

theorem chi_add (a b : ZMod S.N) : chi S (a + b) = chi S a * chi S b := by
  rw [chi, chi, chi, neg_add, ZMod.val_add, ← pow_add]
  exact (pow_eq_pow_mod _ (isPrimitiveRoot_ζN S).pow_eq_one).symm

theorem chi_zero : chi S 0 = 1 := by simp [chi]

theorem chi_ne_one {a : ZMod S.N} (ha : a ≠ 0) : chi S a ≠ 1 := fun h => by
  have h1 := ((isPrimitiveRoot_ζN S).pow_eq_one_iff_dvd _).1 h
  have h2 := Nat.eq_zero_of_dvd_of_lt h1 (ZMod.val_lt _)
  exact ha (neg_eq_zero.1 ((ZMod.val_eq_zero _).1 h2))

theorem proj_eq (T : AddSubgroup S.Gam) [Fintype T] (c : T →+ ZMod S.N) :
    S.proj T c = Ring.inverse (Nat.card T : o) • ∑ t : T, chi S (c t) • S.ρ t := by
  rw [ThetaSys.proj, finsum_eq_sum_of_fintype]
  rfl

variable {S}

theorem isUnit_card {T : AddSubgroup S.Gam} (hT : S.IsoFree T) : IsUnit (Nat.card T : o) := by
  obtain ⟨d, ⟨e⟩⟩ := hT.2
  rw [Nat.card_congr e.toEquiv, Nat.card_fun, Nat.card_zmod, Nat.cast_pow]
  exact S.unit.pow _

theorem ρ_mul_ρ {T : AddSubgroup S.Gam} (hT : S.IsoFree T) (s t : T) :
    S.ρ s * S.ρ t = S.ρ (s + t : T) :=
  S.ρ_add _ _ (by rw [hT.1 s.2 t t.2, smul_zero])

theorem proj_mul_self {T : AddSubgroup S.Gam} (hT : S.IsoFree T) (c : T →+ ZMod S.N) :
    S.proj T c * S.proj T c = S.proj T c := by
  have := Fintype.ofFinite T
  have e : (∑ t : T, chi S (c t) • S.ρ t) * (∑ t : T, chi S (c t) • S.ρ t) =
      (Nat.card T : o) • ∑ t : T, chi S (c t) • S.ρ t := by
    rw [Finset.sum_mul, Nat.card_eq_fintype_card, Nat.cast_smul_eq_nsmul, ← Finset.card_univ, ← Finset.sum_const]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [Finset.mul_sum, ← Equiv.sum_comp (Equiv.addLeft s) fun t : T => chi S (c t) • S.ρ t]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [smul_mul_smul_comm, ρ_mul_ρ hT, ← chi_add, ← map_add]
    rfl
  rw [proj_eq, smul_mul_smul_comm, e, smul_smul, _root_.mul_assoc, Ring.inverse_mul_cancel _ (isUnit_card hT),
    _root_.mul_one]

theorem smul_eq_zero_of_forall {T : AddSubgroup S.Gam} (hT : S.IsoFree T) (t : T)
    (h : ∀ c : T →+ ZMod S.N, c t = 0) : S.r • (t : S.Gam) = 0 := by
  obtain ⟨d, ⟨e⟩⟩ := hT.2
  have h1 : S.r • t = 0 := by
    apply e.injective
    rw [map_nsmul, map_zero]
    funext i
    have h2 := h (((ZMod.castHom (dvd_mul_left S.N S.r) (ZMod S.N)).toAddMonoidHom.comp
      (Pi.evalAddMonoidHom (fun _ => ZMod (S.r * S.N)) i)).comp e.toAddMonoidHom)
    have h3 : ZMod.castHom (dvd_mul_left S.N S.r) (ZMod S.N) (e t i) = 0 := h2
    rw [← ZMod.natCast_zmod_val (e t i), map_natCast, ZMod.natCast_eq_zero_iff] at h3
    obtain ⟨m, hm⟩ := h3
    rw [Pi.smul_apply, Pi.zero_apply, ← ZMod.natCast_zmod_val (e t i), hm, nsmul_eq_mul, ← Nat.cast_mul,
      ZMod.natCast_eq_zero_iff, ← _root_.mul_assoc]
    exact dvd_mul_right _ _
  exact congrArg Subtype.val h1

theorem sum_proj [IsDomain o] {T : AddSubgroup S.Gam} (hT : S.IsoFree T) [Fintype (T →+ ZMod S.N)] :
    ∑ c, S.proj T c = 1 := by
  have := Fintype.ofFinite T
  simp only [proj_eq]
  rw [← Finset.smul_sum, Finset.sum_comm]
  have e1 : ∀ t : T, ∑ c : T →+ ZMod S.N, chi S (c t) • S.ρ t =
      (∑ c : T →+ ZMod S.N, chi S (c t)) • (1 : Matrix S.J S.J o) := by
    intro t
    rw [← Finset.sum_smul]
    by_cases h : ∀ c : T →+ ZMod S.N, c t = 0
    · rw [S.ρ_one _ (smul_eq_zero_of_forall hT t h)]
    · obtain ⟨c, hc⟩ := not_forall.1 h
      rw [sum_eq_zero_of_mul (fun c : T →+ ZMod S.N => chi S (c t)) (fun a b => chi_add S _ _) (chi_ne_one S hc),
        zero_smul, zero_smul]
  have e2 : ∑ c : T →+ ZMod S.N, ∑ t : T, chi S (c t) = Nat.card T := by
    rw [Finset.sum_eq_single 0]
    · simp [chi_zero]
    · intro c _ hc
      obtain ⟨t, ht⟩ := DFunLike.ne_iff.1 hc
      exact sum_eq_zero_of_mul (fun t : T => chi S (c t)) (fun a b => by rw [map_add, chi_add]) (chi_ne_one S ht)
    · simp
  simp only [e1]
  rw [← Finset.sum_smul, Finset.sum_comm, e2, smul_smul, Ring.inverse_mul_cancel _ (isUnit_card hT), one_smul]

theorem FF_mem (T : AddSubgroup S.Gam) (c : T →+ ZMod S.N) (k : _) : S.FF T c k ∈ S.R := by
  have := Fintype.ofFinite T
  rw [ThetaSys.FF, finsum_eq_sum_of_fintype]
  exact sum_mem fun t _ => mul_mem (S.R.algebraMap_mem _)
    (sum_mem fun j _ => mul_mem (S.R.algebraMap_mem _) (S.ev_mem _ _))

end Proj

section Bundle

open DualLattice RatModel

variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {M : RatModel o Ω} {J : Type} [Fintype J] [DecidableEq J]
  (EE : M.Lat J) {Γ : Type} (t : Γ → Ω)

abbrev dualAt (z : M.Z) : Submodule (M.O z) (J → Ω) := dotDual (M.O z) (EE.E z)

def IsSec (a : ℕ) (g : J → Ω) : Prop := ∀ z x, M.Div t x z → (fun j => g j / t x ^ a) ∈ dualAt EE z

def Spans {A : Type} (a : ℕ) (G : A → J → Ω) (z : M.Z) : Prop :=
  ∀ x, M.Div t x z → dualAt EE z ≤ Submodule.span (M.O z) (Set.range fun k j => G k j / t x ^ a)

variable {t}

omit [Fintype J] [DecidableEq J] in
theorem div_pow_mem_of_div {z : M.Z} {N : Submodule (M.O z) (J → Ω)} {x y : Γ} (hx : M.Div t x z) (hy : t y ≠ 0)
    {a : ℕ} {g : J → Ω} (h : (fun j => g j / t y ^ a) ∈ N) : (fun j => g j / t x ^ a) ∈ N := by
  have e : (fun j => g j / t x ^ a) = (⟨t y / t x, hx.2 y⟩ ^ a : M.O z) • fun j => g j / t y ^ a := by
    funext j
    have := hx.1
    simp only [Pi.smul_apply, Subalgebra.smul_def, smul_eq_mul, SubmonoidClass.coe_pow, div_pow]
    field_simp
  rw [e]
  exact N.smul_mem _ h

theorem IsSec.mul_pow {a : ℕ} {g : J → Ω} (h : IsSec EE t a g) (b : ℕ) (y : Γ) :
    IsSec EE t (a + b) fun j => g j * t y ^ b := by
  intro z x hx
  have e : (fun j => g j * t y ^ b / t x ^ (a + b)) =
      (⟨t y / t x, hx.2 y⟩ ^ b : M.O z) • fun j => g j / t x ^ a := by
    funext j
    have := hx.1
    simp only [Pi.smul_apply, Subalgebra.smul_def, smul_eq_mul, SubmonoidClass.coe_pow, div_pow]
    field_simp
    ring
  rw [e]
  exact Submodule.smul_mem _ _ (h z x hx)

theorem Spans.of_mul_pow {A B' : Type} {a : ℕ} {G : A → J → Ω} {z : M.Z} (h : Spans EE t a G z) {b c : ℕ}
    (hc : c = a + b) {G' : B' → J → Ω} (hG : ∀ k y, ∃ l, G' l = fun j => G k j * t y ^ b) : Spans EE t c G' z := by
  intro x hx
  refine (h x hx).trans (Submodule.span_mono ?_)
  rintro _ ⟨k, rfl⟩
  obtain ⟨l, hl⟩ := hG k x
  refine ⟨l, funext fun j => ?_⟩
  have := hx.1
  simp only [hl, hc]
  field_simp
  ring

theorem exists_isSec [IsNoetherianRing o] [Finite Γ] (ht : M.HasDiv t) (I : Finset Γ) (hI : ∀ i ∈ I, t i ≠ 0)
    (g : J → Ω) (hg : ∀ z, (∀ i ∈ I, M.Div t i z) → ∀ x, M.Div t x z → (fun j => g j / t x) ∈ dualAt EE z) :
    ∃ C₀ : ℕ, ∀ C ≥ C₀, IsSec EE t (1 + I.card * C) fun j => (∏ i ∈ I, t i) ^ C * g j := by
  have := M.noetherianSpace_of_isNoetherianRing
  have key := (TopologicalSpace.NoetherianSpace.isCompact (Set.univ : Set M.Z)).induction_on
    (p := fun s => ∃ C₀ : ℕ, ∀ C ≥ C₀, ∀ z ∈ s, ∀ x, M.Div t x z →
      (fun j => (∏ i ∈ I, t i) ^ C * g j / t x ^ (1 + I.card * C)) ∈ dualAt EE z)
    ⟨0, fun _ _ _ h => h.elim⟩ (fun _ _ hst ⟨C₀, h⟩ => ⟨C₀, fun C hC z hz => h C hC z (hst hz)⟩)
    (fun _ _ ⟨C₀, h⟩ ⟨C₁, h'⟩ => ⟨max C₀ C₁, fun C hC z hz =>
      hz.elim (h C ((le_max_left _ _).trans hC) z) (h' C ((le_max_right _ _).trans hC) z)⟩) ?_
  · obtain ⟨C₀, h⟩ := key
    exact ⟨C₀, fun C hC z => h C hC z trivial⟩
  intro z₁ _
  obtain ⟨U, b, hU, -, hb⟩ := EE.loc z₁
  obtain ⟨y, hy⟩ := ht z₁
  let W : M.Z.Opens := U ⊓ ⟨_, M.isOpen_setOf_div t y⟩
  have hW : ∀ l, ∃ C₀ : ℕ, ∀ C ≥ C₀, ∀ z ∈ W, (b l ⬝ᵥ fun j => g j / t y) * (∏ i ∈ I, t i / t y) ^ C ∈ M.O z :=
    fun l => exists_forall_mul_prod_div_pow_mem_O o Ω M Γ t W y (fun z hz => hz.2) I _
      (fun z hz hi => hg z hi y hz.2 _ (by rw [hb z hz.1]; exact Submodule.subset_span ⟨l, rfl⟩)) hI
  choose C₀ hC₀ using hW
  refine ⟨W, mem_nhdsWithin_of_mem_nhds (W.isOpen.mem_nhds ⟨hU, hy⟩), Finset.univ.sup C₀, fun C hC z hz x hx => ?_⟩
  refine div_pow_mem_of_div hx hy.1 ?_
  rw [dualAt, hb z hz.1]
  refine (mem_dotDual_span _ (b : J → J → Ω) _).2 fun l => ?_
  have e : (fun j => (∏ i ∈ I, t i) ^ C * g j / t y ^ (1 + I.card * C)) =
      (∏ i ∈ I, t i / t y) ^ C • fun j => g j / t y := by
    funext j
    have := hy.1
    simp only [Pi.smul_apply, smul_eq_mul, Finset.prod_div_distrib, Finset.prod_const, div_pow, pow_add, pow_mul]
    field_simp
  rw [e, dotProduct_smul, smul_eq_mul, mul_comm]
  exact hC₀ l C ((Finset.le_sup (Finset.mem_univ l)).trans hC) z hz

theorem exists_open_spans [Finite Γ] {A : Type} [Finite A] {a : ℕ} {G : A → J → Ω} {z : M.Z} {x : Γ}
    (hx : M.Div t x z) (h : dualAt EE z ≤ Submodule.span (M.O z) (Set.range fun k j => G k j / t x ^ a)) :
    ∃ U : Set M.Z, IsOpen U ∧ z ∈ U ∧ ∀ z' ∈ U, Spans EE t a G z' := by
  have := Fintype.ofFinite A
  obtain ⟨U, b, hU, hdet, hb⟩ := EE.loc z
  have hB : b * (b⁻¹ᵀ)ᵀ = 1 := by rw [transpose_transpose, mul_nonsing_inv _ (Ne.isUnit hdet)]
  have hD : ∀ z' ∈ U, dualAt EE z' = Submodule.span (M.O z') (Set.range (b⁻¹ᵀ)) := fun z' hz' => by
    rw [dualAt, hb z' hz', dotDual_span_rows _ hB]
  have h1 : ∀ l, ∃ c : A → M.O z, ∑ k, c k • (fun j => G k j / t x ^ a) = b⁻¹ᵀ l := fun l =>
    (Submodule.mem_span_range_iff_exists_fun _).1 (h (by rw [hD z hU]; exact Submodule.subset_span ⟨l, rfl⟩))
  choose c hc using h1
  refine ⟨(U ∩ {z' | M.Div t x z'}) ∩ ⋂ l, ⋂ k, {z' | (c l k : Ω) ∈ M.O z'},
    (U.isOpen.inter (M.isOpen_setOf_div t x)).inter
      (isOpen_iInter_of_finite fun l => isOpen_iInter_of_finite fun k => M.isOpen_setOf_mem_O _),
    ⟨⟨hU, hx⟩, Set.mem_iInter.2 fun l => Set.mem_iInter.2 fun k => (c l k).2⟩, ?_⟩
  rintro z' ⟨⟨hU', hx'⟩, hc'⟩ y hy
  rw [hD z' hU', Submodule.span_le]
  rintro _ ⟨l, rfl⟩
  rw [← hc l]
  refine Submodule.sum_mem _ fun k _ => ?_
  exact Submodule.smul_mem _ (⟨c l k, Set.mem_iInter.1 (Set.mem_iInter.1 hc' l) k⟩ : M.O z')
    (div_pow_mem_of_div hx' hy.1 (Submodule.subset_span ⟨k, rfl⟩))

theorem exists_global [IsNoetherianRing o] [Finite Γ] (R : Subalgebra o Ω) (hR : ∀ x, t x ∈ R)
    (h : ∀ z : M.Z, ∃ U : Set M.Z, IsOpen U ∧ z ∈ U ∧ ∃ (A : Type) (_ : Finite A) (a : ℕ) (G : A → J → Ω),
      (∀ k j, G k j ∈ R) ∧ (∀ k, IsSec EE t a (G k)) ∧ ∀ z' ∈ U, Spans EE t a G z') :
    ∃ (A : Type) (_ : Finite A) (a : ℕ) (G : A → J → Ω),
      (∀ k j, G k j ∈ R) ∧ (∀ k, IsSec EE t a (G k)) ∧ ∀ z, Spans EE t a G z := by
  have := M.noetherianSpace_of_isNoetherianRing
  have key := (TopologicalSpace.NoetherianSpace.isCompact (Set.univ : Set M.Z)).induction_on
    (p := fun s => ∃ (A : Type) (_ : Finite A) (a : ℕ) (G : A → J → Ω),
      (∀ k j, G k j ∈ R) ∧ (∀ k, IsSec EE t a (G k)) ∧ ∀ z ∈ s, Spans EE t a G z)
    ⟨Empty, inferInstance, 0, Empty.elim, fun k => k.elim, fun k => k.elim, fun _ h => h.elim⟩
    (fun _ _ hst ⟨A, hA, a, G, h1, h2, h3⟩ => ⟨A, hA, a, G, h1, h2, fun z hz => h3 z (hst hz)⟩) ?_
    (fun z _ => by
      obtain ⟨U, hU, hz, h'⟩ := h z
      exact ⟨U, mem_nhdsWithin_of_mem_nhds (hU.mem_nhds hz), h'⟩)
  · obtain ⟨A, hA, a, G, h1, h2, h3⟩ := key
    exact ⟨A, hA, a, G, h1, h2, fun z => h3 z trivial⟩
  rintro s s' ⟨A, hA, a, G, h1, h2, h3⟩ ⟨A', hA', a', G', h1', h2', h3'⟩
  refine ⟨(A × Γ) ⊕ (A' × Γ), inferInstance, a + a',
    Sum.elim (fun p j => G p.1 j * t p.2 ^ a') (fun p j => G' p.1 j * t p.2 ^ a), ?_, ?_, ?_⟩
  · rintro (p | p) j
    · exact mul_mem (h1 _ _) (pow_mem (hR _) _)
    · exact mul_mem (h1' _ _) (pow_mem (hR _) _)
  · rintro (p | p)
    · exact (h2 _).mul_pow EE _ _
    · rw [add_comm]
      exact (h2' _).mul_pow EE _ _
  · rintro z (hz | hz)
    · exact (h3 z hz).of_mul_pow EE rfl fun k y => ⟨.inl (k, y), rfl⟩
    · exact (h3' z hz).of_mul_pow EE (add_comm _ _) fun k y => ⟨.inr (k, y), rfl⟩

end Bundle

open DualLattice RatModel in

theorem exists_global_generators : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (M : RatModel o Ω) (U₀ : M.Z.Opens) (EE : M.Lat S.J), S.admitted M U₀ → JacobsonSpace M.Z → ((∀ ξ : M.Z, S.IsoFree (S.TT M ξ) ∧ S.perp (S.TT M ξ) = S.HH M ξ) ∧ (∀ ξ z : M.Z, ξ ⤳ z → S.supI M z ⊆ S.supI M ξ) ∧ (∀ ξ ∈ U₀, S.TT M ξ = ⊥) ∧ (∀ (ξ : M.Z) (W : M.Z.Opens), ξ ∈ W → ∃ x ∈ W, IsClosed ({x} : Set M.Z) ∧ ξ ⤳ x ∧ S.supI M x = S.supI M ξ)) → (∀ (ξ : M.Z) (c : S.TT M ξ →+ ZMod S.N), S.FF (S.TT M ξ) c ≠ 0) → (∀ z : M.Z, IsClosed ({z} : Set M.Z) → EE.E z = Submodule.span (M.O z) {v | ∃ (c : S.TT M z →+ ZMod S.N) (k : _) (x₀ : S.Gam) (i : S.J), M.Div (S.FF (S.TT M z) c) k z ∧ x₀ ∈ S.supI M z ∧ v = fun j => S.th x₀ / S.FF _ c k * algebraMap o Ω (S.proj _ c j i)}) → (∀ (ξ : M.Z) (c : S.TT M ξ →+ ZMod S.N) (k : _) (i : S.J) (z : M.Z), S.supI M ξ ⊆ S.supI M z → ∀ x₀ ∈ S.supI M z, ∀ v ∈ EE.E z, S.FF _ c k / S.th x₀ * ((fun j => algebraMap o Ω (S.proj _ c i j)) ⬝ᵥ v) ∈ M.O z) → ∃ (n a : ℕ) (GG : Fin n → S.J → S.R), ∀ z : M.Z, ∀ x₀ ∈ S.supI M z, ∀ w : S.J → Ω, w ∈ Submodule.span (M.O z) (Set.range fun k j => (GG k j : Ω) / S.th x₀ ^ a) ↔ ∀ v ∈ EE.E z, w ⬝ᵥ v ∈ M.O z := by
  intro o Ω _ _ _ hB S M U₀ EE hAdm _ ⟨hiso, _, _, hcl⟩ hne hE hsec
  have := hB.ded
  have key := exists_global EE (t := S.th) S.R S.th_mem fun ξ => ?_
  · obtain ⟨A, hA, a, G, h1, h2, h3⟩ := key
    obtain ⟨n, ⟨e⟩⟩ := Finite.exists_equiv_fin A
    refine ⟨n, a, fun k j => ⟨G (e.symm k) j, h1 _ _⟩, fun z x hx w => ⟨fun hw v hv => ?_, fun hw => ?_⟩⟩
    · have hle : Submodule.span (M.O z) (Set.range fun k j => G (e.symm k) j / S.th x ^ a) ≤ dualAt EE z := by
        rw [Submodule.span_le]
        rintro _ ⟨k, rfl⟩
        exact h2 _ z x hx
      rw [dotProduct_comm]
      exact hle hw v hv
    · have hw' : w ∈ dualAt EE z := fun v hv => dotProduct_comm w v ▸ hw v hv
      refine Submodule.span_mono ?_ (h3 z x hx hw')
      rintro _ ⟨k, rfl⟩
      exact ⟨e k, by simp⟩
  obtain ⟨z, -, hz, hξ, -⟩ := hcl ξ ⊤ trivial
  have hT := (hiso z).1
  have : Finite (S.TT M z →+ ZMod S.N) := DFunLike.finite _
  have := Fintype.ofFinite (S.TT M z →+ ZMod S.N)
  choose k hk using fun c => hAdm.2 _ c hT (hne z c) z
  obtain ⟨x, hx⟩ := hAdm.1.div z
  let I : Finset S.Gam := (Set.toFinite (S.supI M z)).toFinset
  have hI : ∀ i ∈ I, M.Div S.th i z := fun i hi => ((Set.toFinite (S.supI M z)).mem_toFinset).1 hi
  let g : (S.TT M z →+ ZMod S.N) × S.J → S.J → Ω := fun p j =>
    S.FF _ p.1 (k p.1) * algebraMap o Ω (S.proj _ p.1 p.2 j)
  have hg : ∀ p, ∃ C₀ : ℕ, ∀ C ≥ C₀, IsSec EE S.th (1 + I.card * C) fun j => (∏ i ∈ I, S.th i) ^ C * g p j := by
    intro p
    refine exists_isSec EE hAdm.1.div I (fun i hi => (hI i hi).1) (g p) fun z' hz' y hy v hv => ?_
    have h := hsec z p.1 (k p.1) p.2 z' (fun i hi => hz' i (((Set.toFinite (S.supI M z)).mem_toFinset).2 hi)) y hy v hv
    convert h using 1
    simp only [dotProduct, Finset.mul_sum, g]
    exact Finset.sum_congr rfl fun j _ => by ring
  choose C₀ hC₀ using hg
  let C := Finset.univ.sup C₀
  have hspan : dualAt EE z ≤ Submodule.span (M.O z)
      (Set.range fun p j => (∏ i ∈ I, S.th i) ^ C * g p j / S.th x ^ (1 + I.card * C)) := by
    intro w hw
    let P : (S.TT M z →+ ZMod S.N) → Matrix S.J S.J Ω := fun c => (algebraMap o Ω).mapMatrix (S.proj _ c)
    have hP : ∑ c, P c * P c = 1 := by
      simp only [P, ← map_mul, proj_mul_self hT, ← map_sum, sum_proj hT, map_one]
    have e : w = ∑ c, ∑ i, (w ᵥ* P c) i • P c i := by
      simp only [← vecMul_eq_sum, vecMul_vecMul]
      rw [← vecMul_sum, hP, vecMul_one]
    rw [e]
    refine Submodule.sum_mem _ fun c _ => Submodule.sum_mem _ fun i _ => ?_
    have h1 : S.th x / S.FF _ c (k c) * (w ᵥ* P c) i ∈ M.O z := by
      have h := hw (fun j => S.th x / S.FF _ c (k c) * algebraMap o Ω (S.proj _ c j i))
        (by rw [hE z hz]; exact Submodule.subset_span ⟨c, k c, x, i, hk c, hx, rfl⟩)
      convert h using 1
      simp only [vecMul, dotProduct, Finset.mul_sum, P, RingHom.mapMatrix_apply, map_apply]
      exact Finset.sum_congr rfl fun j _ => by ring
    have h2 : (∏ i ∈ I, S.th x / S.th i) ^ C ∈ M.O z := pow_mem (prod_mem fun i hi => (hI i hi).2 x) _
    have e2 : (w ᵥ* P c) i • P c i = (⟨_, mul_mem h1 h2⟩ : M.O z) •
        fun j => (∏ i ∈ I, S.th i) ^ C * g (c, i) j / S.th x ^ (1 + I.card * C) := by
      funext j
      have h3 := hx.1
      have h4 := (hk c).1
      have h5 : (∏ i ∈ I, S.th i) ≠ 0 := Finset.prod_ne_zero_iff.2 fun i hi => (hI i hi).1
      simp only [Pi.smul_apply, Subalgebra.smul_def, smul_eq_mul, Finset.prod_div_distrib, Finset.prod_const, div_pow,
        pow_add, pow_mul, g]
      have h6 : P c i j = algebraMap o Ω (S.proj _ c i j) := rfl
      rw [h6]
      field_simp
    rw [e2]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨(c, i), rfl⟩)
  obtain ⟨U, hU, hzU, h⟩ := exists_open_spans EE hx hspan
  refine ⟨U, hU, hξ.mem_open hU hzU, _, inferInstance, _, _, fun p j => ?_,
    fun p => hC₀ p C (Finset.le_sup (Finset.mem_univ p)), h⟩
  exact mul_mem (pow_mem (prod_mem fun i _ => S.th_mem i) _) (mul_mem (FF_mem _ _ _) (S.R.algebraMap_mem _))

end GlobalTheory.ZH.GlobalGen
end

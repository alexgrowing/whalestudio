import Mathlib
import Development.AbelianVarietyTheory.Definitions.Degenerations.ArithBase
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.OrthogonalFreeOfPerfectAltZmod

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical

namespace GlobalTheory.ThetaProj

theorem eStd_swap (g n : ℕ) (a b : Fin g ⊕ Fin g → ZMod n) : eStd g n a b = -eStd g n b a := by
  simp only [eStd]
  rw [← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun i _ => by ring

theorem exists_eStd_eq (g n : ℕ) (f : (Fin g ⊕ Fin g → ZMod n) →ₗ[ZMod n] ZMod n) :
    ∃ b, ∀ y, eStd g n b y = f y := by
  refine ⟨Sum.elim (fun i => f (Pi.single (.inr i) 1)) (fun i => -f (Pi.single (.inl i) 1)),
    fun y => ?_⟩
  conv_rhs => rw [← Finset.univ_sum_single y, map_sum, Fintype.sum_sum_type,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  have h : ∀ j, f (Pi.single j (y j)) = y j * f (Pi.single j 1) := fun j => by
    rw [← smul_eq_mul, ← map_smul, ← Pi.single_smul, smul_eq_mul, _root_.mul_one]
  rw [h, h]
  simp only [Sum.elim_inl, Sum.elim_inr]
  ring

theorem exists_retraction {n d : ℕ} [NeZero n] {Γ : Type} [AddCommGroup Γ] [Module (ZMod n) Γ]
    (T : AddSubgroup Γ) (e : T ≃+ (Fin d → ZMod n)) : ∃ p : Γ →+ T, ∀ t : T, p t = t := by
  let T' : Submodule (ZMod n) Γ := AddSubgroup.toZModSubmodule n T
  let e' : T' →+ (Fin d → ZMod n) :=
    { toFun := fun x => e ⟨x.1, x.2⟩
      map_zero' := map_zero e
      map_add' := fun x y => map_add e ⟨x.1, x.2⟩ ⟨y.1, y.2⟩ }
  obtain ⟨f, hf⟩ := (ZModPerp.baer_of_free (n := n) (Fin d → ZMod n)).extension_property
    T'.subtype T'.subtype_injective (e'.toZModLinearMap n)
  refine ⟨e.symm.toAddMonoidHom.comp f.toAddMonoidHom, fun t => ?_⟩
  have : f t = e t := LinearMap.congr_fun hf ⟨t.1, t.2⟩
  simp [this]

theorem nsmul_eq_zero_of_forall_char {r N : ℕ} [NeZero (r * N)] {Γ : Type} [AddCommGroup Γ]
    [Module (ZMod (r * N)) Γ] (u : Γ) (h : ∀ ψ : Γ →+ ZMod N, ψ u = 0) : r • u = 0 := by
  by_contra hu
  obtain ⟨f, hf⟩ := ZModPerp.exists_dual_ne_zero (n := r * N) hu
  apply hf
  have h1 := h ((ZMod.castHom (dvd_mul_left N r) (ZMod N)).toAddMonoidHom.comp f.toAddMonoidHom)
  have h2 : ZMod.castHom (dvd_mul_left N r) (ZMod N) (f u) = 0 := h1
  rw [← ZMod.natCast_zmod_val (f u), map_natCast, ZMod.natCast_eq_zero_iff] at h2
  obtain ⟨k, hk⟩ := h2
  rw [map_nsmul, ← ZMod.natCast_zmod_val (f u), hk, nsmul_eq_mul, ← Nat.cast_mul, ← _root_.mul_assoc,
    Nat.cast_mul, ZMod.natCast_self, zero_mul]

theorem sum_char_smul {o M U : Type} [CommRing o] [IsDomain o] [AddCommGroup M] [Module o M]
    [AddCommGroup U] [Fintype U] {N : ℕ} [NeZero N] [Fintype (U →+ ZMod N)]
    (χ : AddChar (ZMod N) o) (hχ : ∀ a, χ a = 1 → a = 0) (ρ : U → M)
    (hρ : ∀ u, (∀ ψ : U →+ ZMod N, ψ u = 0) → ρ u = ρ 0) :
    ∑ ψ : U →+ ZMod N, ∑ u, χ (-ψ u) • ρ u = (Fintype.card U : o) • ρ 0 := by
  have h1 : ∀ u, (∑ ψ : U →+ ZMod N, χ (-ψ u)) • ρ u
      = (∑ ψ : U →+ ZMod N, χ (-ψ u)) • ρ 0 := fun u => by
    by_cases hu : ∀ ψ : U →+ ZMod N, ψ u = 0
    · rw [hρ u hu]
    · obtain ⟨ψ, hψ⟩ := not_forall.mp hu
      have : χ.compAddMonoidHom (-(AddMonoidHom.eval u : (U →+ ZMod N) →+ ZMod N)) ≠ 1 := by
        intro h
        have := DFunLike.congr_fun h ψ
        exact hψ (neg_eq_zero.mp (hχ _ this))
      have h0 : ∑ ψ : U →+ ZMod N, χ (-ψ u) = 0 := AddChar.sum_eq_zero_of_ne_one this
      rw [h0, zero_smul, zero_smul]
  have h2 : ∀ ψ : U →+ ZMod N, ψ ≠ 0 → ∑ u, χ (-ψ u) = 0 := fun ψ hψ => by
    have : χ.compAddMonoidHom (-ψ) ≠ 1 := by
      intro h
      apply hψ
      ext u
      have := DFunLike.congr_fun h u
      exact neg_eq_zero.mp (hχ _ this)
    exact AddChar.sum_eq_zero_of_ne_one this
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_smul, h1]
  rw [← Finset.sum_smul, Finset.sum_comm,
    Finset.sum_eq_single (0 : U →+ ZMod N) (fun ψ _ => h2 ψ) (by simp)]
  simp

theorem sum_ext_char_smul {o M A T : Type} [CommRing o] [IsDomain o] [AddCommGroup M] [Module o M]
    [AddCommGroup A] [AddCommGroup T] [Finite A] [Finite T] {N : ℕ} [NeZero N]
    (i : A →+ T) (p : T →+ A) (hp : ∀ a, p (i a) = a)
    (χ : AddChar (ZMod N) o) (hχ : ∀ a, χ a = 1 → a = 0) (ρ : T → M)
    (hρ : ∀ a u, (∀ ψ : T →+ ZMod N, ψ u = 0) → ρ (i a + u) = ρ (i a)) (c' : A →+ ZMod N) :
    Nat.card T = Nat.card A * Nat.card p.ker ∧
    ∑ᶠ c ∈ {c : T →+ ZMod N | c.comp i = c'}, ∑ᶠ t, χ (-c t) • ρ t
      = (Nat.card p.ker : o) • ∑ᶠ a, χ (-c' a) • ρ (i a) := by
  let q : T →+ p.ker := (AddMonoidHom.id T - i.comp p).codRestrict p.ker fun t => by
    simp [AddMonoidHom.mem_ker, hp]
  have hq : ∀ t, (q t : T) = t - i (p t) := fun t => rfl
  have hqu : ∀ u : p.ker, q u = u := fun u => Subtype.ext (by
    rw [hq, (AddMonoidHom.mem_ker).mp u.2, map_zero, sub_zero])
  have hqi : ∀ a, q (i a) = 0 := fun a => Subtype.ext (by rw [hq, hp, sub_self]; rfl)
  let e : A × p.ker ≃ T :=
    { toFun := fun x => i x.1 + x.2
      invFun := fun t => (p t, q t)
      left_inv := fun x => by
        simp [hp, hqu, hqi, (AddMonoidHom.mem_ker).mp x.2.2]
      right_inv := fun t => by simp [hq] }
  have he : ∀ a (u : p.ker), e (a, u) = i a + u := fun _ _ => rfl
  refine ⟨by rw [← Nat.card_prod, Nat.card_congr e], ?_⟩
  have := Fintype.ofFinite A
  have := Fintype.ofFinite T
  have := Fintype.ofFinite p.ker
  have : Finite (p.ker →+ ZMod N) := DFunLike.finite _
  have := Fintype.ofFinite (p.ker →+ ZMod N)
  have hinj : Function.Injective fun ψ : p.ker →+ ZMod N => c'.comp p + ψ.comp q := by
    intro ψ ψ' h
    ext u
    have := DFunLike.congr_fun (add_left_cancel h) (u : T)
    simpa [hqu] using this
  have hs : {c : T →+ ZMod N | c.comp i = c'}
      = Set.range fun ψ : p.ker →+ ZMod N => c'.comp p + ψ.comp q := by
    ext c
    constructor
    · rintro rfl
      refine ⟨c.comp p.ker.subtype, ?_⟩
      ext t
      simp [hq]
    · rintro ⟨ψ, rfl⟩
      ext a
      simp [hp, hqi]
  rw [hs, finsum_mem_range hinj]
  simp_rw [finsum_eq_sum_of_fintype, ← e.sum_comp, Fintype.sum_prod_type, he]
  rw [Finset.sum_comm, Finset.smul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  have := sum_char_smul χ hχ (fun u : p.ker => ρ (i a + u)) fun u hu => by
    have := hρ a u fun ψ => hu (ψ.comp p.ker.subtype)
    simpa using this
  simp only [ZeroMemClass.coe_zero, add_zero] at this
  rw [smul_comm, Nat.card_eq_fintype_card, ← this, Finset.smul_sum]
  refine Finset.sum_congr rfl fun ψ _ => ?_
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [smul_smul, ← AddChar.map_add_eq_mul]
  simp [hp, hqu, hqi, (AddMonoidHom.mem_ker).mp u.2, add_comm]

end GlobalTheory.ThetaProj

namespace GlobalTheory

open ThetaProj

theorem thetaSys_FF_mem_finite_perp_proj :
    ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω),
      (∀ T c k, S.FF T c k ∈ S.R) ∧ Set.Finite {x : Ω | ∃ T c k, x = S.FF T c k} ∧
      (∀ H, S.perp (S.perp H) = H) ∧
      ∀ (T T' : AddSubgroup S.Gam) (h : T' ≤ T), S.IsoFree T → S.IsoFree T' →
        ∀ (c' : T' →+ ZMod S.N), S.proj T' c' =
          ∑ᶠ c ∈ {c : T →+ ZMod S.N | c.comp (AddSubgroup.inclusion h) = c'}, S.proj T c := by
  intro o Ω _ _ _ hA S
  have hN := S.N_ge
  have hr := S.r_pos
  have : NeZero S.N := ⟨by omega⟩
  have : NeZero (S.r * S.N) := ⟨Nat.mul_ne_zero (by omega) (by omega)⟩
  have : NeZero ((S.r * S.N) ^ 2) := ⟨pow_ne_zero _ (NeZero.ne _)⟩
  have : IsDomain o := hA.inj.isDomain _
  refine ⟨fun T c k => ?_, ?_, fun H => ?_, fun T T' h hT hT' c' => ?_⟩
  · have := Fintype.ofFinite T
    rw [ThetaSys.FF, finsum_eq_sum_of_fintype]
    exact S.R.sum_mem fun t _ => S.R.mul_mem (S.R.algebraMap_mem _)
      (S.R.sum_mem fun j _ => S.R.mul_mem (S.R.algebraMap_mem _) (S.ev_mem _ _))
  · have : Finite (AddSubgroup S.Gam) := Finite.of_injective _ SetLike.coe_injective
    have : ∀ T : AddSubgroup S.Gam, Finite (T →+ ZMod S.N) := fun T => DFunLike.finite _
    refine (Set.finite_range fun x : Σ T : AddSubgroup S.Gam,
      (T →+ ZMod S.N) × (S.J × (T → ZMod ((S.r * S.N) ^ 2))) => S.FF x.1 x.2.1 x.2.2).subset ?_
    rintro x ⟨T, c, k, rfl⟩
    exact ⟨⟨T, c, k⟩, rfl⟩
  · refine le_antisymm (fun x hx => ?_) fun x hx y hy => ?_
    · by_contra hxH
      let H' : Submodule (ZMod (S.r * S.N)) S.Gam := AddSubgroup.toZModSubmodule _ H
      obtain ⟨f, hf⟩ := ZModPerp.exists_dual_ne_zero (n := S.r * S.N) (q := H'.mkQ x)
        (fun h0 => hxH ((Submodule.Quotient.mk_eq_zero H').mp h0))
      obtain ⟨b, hb⟩ := exists_eStd_eq _ _ (f ∘ₗ H'.mkQ)
      have hb' : b ∈ S.perp H := fun y hy => by
        rw [hb, LinearMap.comp_apply, Submodule.mkQ_apply,
          (Submodule.Quotient.mk_eq_zero H').mpr hy, map_zero]
      have h1 : eStd S.g _ x b = 0 := hx b hb'
      rw [eStd_swap, neg_eq_zero, hb] at h1
      exact hf h1
    · rw [eStd_swap, hy x hx, neg_zero]
  · obtain ⟨d, ⟨e⟩⟩ := hT.2
    obtain ⟨d', ⟨e'⟩⟩ := hT'.2
    obtain ⟨p, hp⟩ := exists_retraction T' e'
    have hζ : IsPrimitiveRoot S.ζN S.N :=
      S.prim.pow (NeZero.pos _) (by ring)
    let χ : AddChar (ZMod S.N) o := AddChar.zmodChar S.N hζ.pow_eq_one
    have hχ : ∀ a, χ a = 1 → a = 0 := fun a ha =>
      ((AddChar.zmodChar_primitive_of_primitive_root S.N hζ).zmod_char_eq_one_iff S.N a).mp ha
    let _ : Module (ZMod (S.r * S.N)) T := AddCommGroup.zmodModule fun x => Subtype.ext (by
      rw [AddSubgroup.coe_nsmul, ← Nat.cast_smul_eq_nsmul (ZMod (S.r * S.N)), ZMod.natCast_self,
        zero_smul]
      rfl)
    obtain ⟨h1, h2⟩ := sum_ext_char_smul (AddSubgroup.inclusion h) (p.comp T.subtype)
      (fun a => hp a) χ hχ (fun t : T => S.ρ t) (fun a u hu => by
        have hu' : S.r • (u : S.Gam) = 0 :=
          congrArg Subtype.val (nsmul_eq_zero_of_forall_char (r := S.r) u hu)
        rw [AddSubgroup.coe_add, ← S.ρ_add _ _ (by
          rw [hT.1 (AddSubgroup.inclusion h a).2 u u.2, smul_zero]), S.ρ_one _ hu', _root_.mul_one]) c'
    have hu : IsUnit (Nat.card T : o) := by
      rw [Nat.card_congr e.toEquiv, Nat.card_fun, Nat.card_zmod, Nat.cast_pow]
      exact S.unit.pow _
    have hfin : Finite (T →+ ZMod S.N) := DFunLike.finite _
    have h3 : ∑ᶠ c ∈ {c : T →+ ZMod S.N | c.comp (AddSubgroup.inclusion h) = c'}, S.proj T c
        = Ring.inverse (Nat.card T : o) •
          ∑ᶠ c ∈ {c : T →+ ZMod S.N | c.comp (AddSubgroup.inclusion h) = c'},
            ∑ᶠ t : T, χ (-c t) • S.ρ t := by
      rw [finsum_mem_eq_finite_toFinset_sum _ (Set.toFinite _),
        finsum_mem_eq_finite_toFinset_sum _ (Set.toFinite _), Finset.smul_sum]
      rfl
    rw [h3, h2, smul_smul]
    rw [h1, Nat.cast_mul] at hu ⊢
    rw [Ring.mul_inverse_rev' (Commute.all _ _), mul_right_comm,
      Ring.inverse_mul_cancel _ (isUnit_of_mul_isUnit_right hu), _root_.one_mul]
    rfl

end GlobalTheory

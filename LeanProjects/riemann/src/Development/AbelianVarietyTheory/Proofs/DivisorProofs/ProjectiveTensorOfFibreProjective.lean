import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorModOfTmul
open scoped TensorProduct

set_option autoImplicit false

noncomputable section

open scoped TensorProduct

namespace GlobalTheory.HTSummand

theorem isNilpotent_matrix_of_entries_mem {R : Type*} [CommRing R] {n : ℕ} (I : Ideal R) (N : ℕ)
    (hN : I ^ N = ⊥) (M : Matrix (Fin n) (Fin n) R) (hM : ∀ i j, M i j ∈ I) : IsNilpotent M := by
  have key : ∀ j : ℕ, ∀ a b, (M ^ j) a b ∈ I ^ j := by
    intro j
    induction j with
    | zero => intro a b; rw [pow_zero, Ideal.one_eq_top]; exact Submodule.mem_top
    | succ j ih =>
      intro a b
      rw [pow_succ M, Matrix.mul_apply, pow_succ I]
      exact Ideal.sum_mem _ fun c _ => Ideal.mul_mem_mul (ih a c) (hM c b)
  refine ⟨N, ?_⟩
  ext a b
  have := key N a b
  rw [hN, Ideal.mem_bot] at this
  simpa using this

theorem le_pow_smul_of_le_smul {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] (I : Ideal R)
    (K : Submodule R M) (hK : K ≤ I • K) (j : ℕ) : K ≤ (I ^ j) • K := by
  induction j with
  | zero => rw [pow_zero, Ideal.one_eq_top, Submodule.top_smul]
  | succ j ih =>
    rw [pow_succ', Submodule.mul_smul]
    exact hK.trans (Submodule.smul_mono le_rfl ih)

end GlobalTheory.HTSummand

namespace GlobalTheory.HTSummand

theorem projective_tensor_of_fibre_projective :
    ∀ (C k B : Type) [CommRing C] [IsLocalRing C] [IsArtinianRing C] [Field k] [CommRing B] (σ : C →+* k),
      Function.Surjective σ → ∀ (H V : Type 1) [AddCommGroup H] [Module C H] [AddCommGroup V] [Module k V]
      (ρ : B →+* Module.End C H) (ρ' : B →+* Module.End k V) (f : H →ₛₗ[σ] V), Module.Finite C H →
      Module.Projective C H → Function.Surjective f →
      (∀ h, f h = 0 → h ∈ RingHom.ker σ • (⊤ : Submodule C H)) → (∀ x h, f (ρ x h) = ρ' x (f h)) →
      (letI := GlobalTheory.HTSummand.tensorModOf ρ'; Module.Projective (k ⊗[ℤ] B) V) →
      letI := GlobalTheory.HTSummand.tensorModOf ρ; Module.Projective (C ⊗[ℤ] B) H := by
  intro C k B _ _ _ _ _ σ hσ H V _ _ _ _ ρ ρ' f hfin hproj hf hker hcomm hV
  letI mH : Module (C ⊗[ℤ] B) H := tensorModOf ρ
  letI mV : Module (k ⊗[ℤ] B) V := tensorModOf ρ'

  set m : Ideal C := RingHom.ker σ with hm_def
  have hmtop : m ≠ ⊤ := by
    intro h
    have : (1 : C) ∈ m := h ▸ Submodule.mem_top
    rw [hm_def, RingHom.mem_ker, map_one] at this
    exact one_ne_zero this
  have hmjac : m ≤ (⊥ : Ideal C).jacobson := by
    rw [IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top]
    exact IsLocalRing.le_maximalIdeal hmtop
  obtain ⟨N, hN⟩ : ∃ N : ℕ, m ^ N = ⊥ := by
    obtain ⟨N, hN⟩ := IsArtinianRing.isNilpotent_jacobson_bot (R := C)
    exact ⟨N, le_bot_iff.1 ((Ideal.pow_right_mono hmjac N).trans (le_of_eq hN))⟩

  let τa := Algebra.TensorProduct.map σ.toIntAlgHom (AlgHom.id ℤ B)
  let τ : C ⊗[ℤ] B →+* k ⊗[ℤ] B := τa.toRingHom
  have hτ : Function.Surjective τ :=
    Algebra.TensorProduct.map_surjective σ.toIntAlgHom (AlgHom.id ℤ B) hσ Function.surjective_id
  have hτtmul : ∀ (c : C) (b : B), τ (c ⊗ₜ b) = σ c ⊗ₜ b := fun _ _ => rfl
  have hkerτ : RingHom.ker τ ≤ Ideal.map (algebraMap C (C ⊗[ℤ] B)) m := by
    have h1 : RingHom.ker τ = Ideal.map Algebra.TensorProduct.includeLeft m :=
      Algebra.TensorProduct.rTensor_ker σ.toIntAlgHom hσ
    rw [h1]
    exact Ideal.map_le_iff_le_comap.2 fun c hc => Ideal.mem_map_of_mem (algebraMap C (C ⊗[ℤ] B)) hc
  have hJm : ∀ x ∈ RingHom.ker τ, x ∈ (m • ⊤ : Submodule C (C ⊗[ℤ] B)) := by
    intro x hx
    rw [Ideal.smul_top_eq_map, Submodule.restrictScalars_mem]
    exact hkerτ hx
  have hJN : (RingHom.ker τ) ^ N = ⊥ := by
    refine le_bot_iff.1 ((Ideal.pow_right_mono hkerτ N).trans ?_)
    rw [← Ideal.map_pow, hN, Ideal.map_bot]

  haveI tC : IsScalarTower C (C ⊗[ℤ] B) H := IsScalarTower.of_algebraMap_smul fun c h => by
    show ((c ⊗ₜ[ℤ] (1 : B) : C ⊗[ℤ] B)) • h = c • h
    rw [tensorModOf_tmul, map_one]
    rfl
  letI mRV : Module (C ⊗[ℤ] B) V := Module.compHom V τ
  let fR : H →ₗ[C ⊗[ℤ] B] V :=
    { toFun := f
      map_add' := f.map_add
      map_smul' := fun r h => by
        show f (r • h) = τ r • f h
        induction r using TensorProduct.induction_on with
        | zero => rw [zero_smul, map_zero, map_zero, zero_smul]
        | tmul c b =>
          rw [hτtmul, tensorModOf_tmul, tensorModOf_tmul, f.map_smulₛₗ, hcomm]
        | add x y hx hy => rw [add_smul, map_add, hx, hy, map_add, add_smul] }
  have hfR : Function.Surjective fR := hf
  haveI : Module.Finite (C ⊗[ℤ] B) H := Module.Finite.of_restrictScalars_finite C (C ⊗[ℤ] B) H
  haveI : Module.Finite (C ⊗[ℤ] B) V := Module.Finite.of_surjective fR hfR
  haveI finSV : Module.Finite (k ⊗[ℤ] B) V := by
    letI : Algebra (C ⊗[ℤ] B) (k ⊗[ℤ] B) := τ.toAlgebra
    haveI : IsScalarTower (C ⊗[ℤ] B) (k ⊗[ℤ] B) V := IsScalarTower.of_algebraMap_smul fun r v => rfl
    exact Module.Finite.of_restrictScalars_finite (C ⊗[ℤ] B) (k ⊗[ℤ] B) V

  obtain ⟨n, pb, hpb⟩ := Module.Finite.exists_fin' (k ⊗[ℤ] B) V
  obtain ⟨sb, hsb⟩ := Module.projective_lifting_property pb LinearMap.id hpb
  have hps : ∀ v, pb (sb v) = v := fun v => LinearMap.congr_fun hsb v
  set eb : Matrix (Fin n) (Fin n) (k ⊗[ℤ] B) := LinearMap.toMatrix' (sb ∘ₗ pb) with heb
  have heb_idem : IsIdempotentElem eb := by
    show eb * eb = eb
    rw [heb, ← LinearMap.toMatrix'_comp]
    congr 1
    apply LinearMap.ext
    intro y
    simp only [LinearMap.comp_apply, hps]
  have heb_apply : ∀ y, eb.mulVec y = sb (pb y) := fun y => by
    rw [heb, ← Matrix.toLin'_apply, Matrix.toLin'_toMatrix']
    rfl
  obtain ⟨E, hE, hEeb⟩ := exists_isIdempotentElem_eq_of_ker_isNilpotent (τ.mapMatrix :
      Matrix (Fin n) (Fin n) (C ⊗[ℤ] B) →+* Matrix (Fin n) (Fin n) (k ⊗[ℤ] B))
    (fun x hx => by
      refine isNilpotent_matrix_of_entries_mem (RingHom.ker τ) N hJN x fun i j => ?_
      rw [RingHom.mem_ker] at hx ⊢
      exact congrFun (congrFun hx i) j)
    eb ⟨eb.map (Function.surjInv hτ), by ext i j; simp [Function.surjInv_eq hτ]⟩ heb_idem
  have hEE : ∀ w, E.mulVec (E.mulVec w) = E.mulVec w := fun w => by
    rw [Matrix.mulVec_mulVec, hE.eq]
  have hτE : ∀ w : Fin n → C ⊗[ℤ] B, (fun i => τ (E.mulVec w i)) = sb (pb (fun i => τ (w i))) := by
    intro w
    rw [← heb_apply, ← hEeb]
    funext i
    exact RingHom.map_mulVec τ E w i

  set Q : Submodule (C ⊗[ℤ] B) (Fin n → C ⊗[ℤ] B) := LinearMap.range (Matrix.toLin' E) with hQ
  have hQE : ∀ q : Q, E.mulVec (q : Fin n → C ⊗[ℤ] B) = q := by
    rintro ⟨q, w, rfl⟩
    show E.mulVec (Matrix.toLin' E w) = Matrix.toLin' E w
    rw [Matrix.toLin'_apply, hEE]
  let sQ : (Fin n → C ⊗[ℤ] B) →ₗ[C ⊗[ℤ] B] Q :=
    (Matrix.toLin' E).codRestrict Q fun w => LinearMap.mem_range_self _ w
  have hsQ : ∀ q : Q, sQ q = q := fun q => Subtype.ext (by
    show Matrix.toLin' E (q : Fin n → C ⊗[ℤ] B) = q
    rw [Matrix.toLin'_apply, hQE])
  haveI hQproj : Module.Projective (C ⊗[ℤ] B) Q :=
    Module.Projective.of_split Q.subtype sQ (LinearMap.ext hsQ)
  let φ : Q →ₗ[C ⊗[ℤ] B] V :=
    { toFun := fun q => pb (fun i => τ ((q : Fin n → C ⊗[ℤ] B) i))
      map_add' := fun x y => by
        rw [← map_add]
        congr 1
        funext i
        simp
      map_smul' := fun r x => by
        show pb _ = τ r • pb _
        rw [← map_smul]
        congr 1
        funext i
        simp }
  have hφ : Function.Surjective φ := by
    intro v
    let w : Fin n → C ⊗[ℤ] B := fun i => Function.surjInv hτ (sb v i)
    refine ⟨⟨Matrix.toLin' E w, LinearMap.mem_range_self _ w⟩, ?_⟩
    show pb (fun i => τ (Matrix.toLin' E w i)) = v
    rw [Matrix.toLin'_apply, hτE]
    have : (fun i => τ (w i)) = sb v := funext fun i => Function.surjInv_eq hτ _
    rw [this, hps, hps]
  obtain ⟨g, hg⟩ := Module.projective_lifting_property fR φ hfR
  have hgφ : ∀ q, f (g q) = φ q := fun q => LinearMap.congr_fun hg q

  have hgs : Function.Surjective g := by
    have hle : (⊤ : Submodule C H) ≤ (LinearMap.range g).restrictScalars C ⊔ m • ⊤ := by
      intro h _
      obtain ⟨q, hq⟩ := hφ (f h)
      have h0 : f (h - g q) = 0 := by rw [map_sub, hgφ, hq, sub_self]
      have : h = g q + (h - g q) := by abel
      rw [this]
      exact Submodule.add_mem_sup (LinearMap.mem_range_self g q) (hker _ h0)
    have htop := Submodule.le_of_le_smul_of_le_jacobson_bot Module.Finite.fg_top hmjac hle
    intro h
    exact htop Submodule.mem_top

  let g' : Q →ₗ[C] H := g.restrictScalars C
  obtain ⟨s, hs⟩ := Module.projective_lifting_property g' LinearMap.id hgs
  have hgs' : ∀ h, g' (s h) = h := fun h => LinearMap.congr_fun hs h
  let P : Q →ₗ[C] Q := LinearMap.id - s ∘ₗ g'
  have hPK : ∀ x, P x ∈ LinearMap.ker g' := fun x => by
    rw [LinearMap.mem_ker]
    show g' (x - s (g' x)) = 0
    rw [map_sub, hgs', sub_self]
  have hKm : ∀ x ∈ LinearMap.ker g', x ∈ (m • ⊤ : Submodule C Q) := by
    intro x hx
    rw [LinearMap.mem_ker] at hx
    have hφx : φ x = 0 := by rw [← hgφ]; exact (congrArg f hx).trans (map_zero f)
    have hτx : (fun i => τ ((x : Fin n → C ⊗[ℤ] B) i)) = 0 := by
      have h1 := hτE x
      rw [hQE x] at h1
      rw [h1]
      have : pb (fun i => τ ((x : Fin n → C ⊗[ℤ] B) i)) = 0 := hφx
      rw [this, map_zero]
    have hx1 : (x : Fin n → C ⊗[ℤ] B) ∈ (m • ⊤ : Submodule C (Fin n → C ⊗[ℤ] B)) := by
      rw [← Finset.univ_sum_single (x : Fin n → C ⊗[ℤ] B)]
      refine Submodule.sum_mem _ fun i _ => ?_
      have hi : (x : Fin n → C ⊗[ℤ] B) i ∈ (m • ⊤ : Submodule C (C ⊗[ℤ] B)) :=
        hJm _ (RingHom.mem_ker.2 (congrFun hτx i))
      have := Submodule.mem_map_of_mem (f := LinearMap.single C (fun _ : Fin n => C ⊗[ℤ] B) i) hi
      rw [Submodule.map_smul''] at this
      exact Submodule.smul_mono le_rfl le_top this
    have := Submodule.mem_map_of_mem (f := sQ.restrictScalars C) hx1
    rw [Submodule.map_smul''] at this
    have hx' : sQ.restrictScalars C x = x := hsQ x
    rw [hx'] at this
    exact Submodule.smul_mono le_rfl le_top this
  have hK : LinearMap.ker g' ≤ m • LinearMap.ker g' := by
    intro x hx
    have hPx : P x = x := by
      show x - s (g' x) = x
      rw [LinearMap.mem_ker.1 hx, map_zero, sub_zero]
    have := Submodule.mem_map_of_mem (f := P) (hKm x hx)
    rw [Submodule.map_smul'', hPx] at this
    exact Submodule.smul_mono le_rfl (fun y hy => by
      obtain ⟨z, _, rfl⟩ := hy
      exact hPK z) this
  have hK0 : LinearMap.ker g' = ⊥ := by
    have := le_pow_smul_of_le_smul m _ hK N
    rw [hN, Submodule.bot_smul] at this
    exact le_bot_iff.1 this
  have hgi : Function.Injective g := by
    have h' : Function.Injective g' := LinearMap.ker_eq_bot.1 hK0
    exact h'
  exact Module.Projective.of_equiv (LinearEquiv.ofBijective g ⟨hgi, hgs⟩)

end GlobalTheory.HTSummand

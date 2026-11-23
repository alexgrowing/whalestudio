import Mathlib
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.FstHomCompSqzOfLeibniz
import ReciprocityTheory.DualLattices.EvCotStatement

noncomputable section

open TensorProduct IsLocalRing Matrix ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Be2

namespace GlobalTheory.CotUniv

section Ring

variable (O : Type) [CommRing O] (M : Type) [AddCommGroup M] [Module O M]

def SqExt : Type := TrivSqZeroExt O M

instance : CommRing (SqExt O M) :=
  letI : Module Oᵐᵒᵖ M := Module.compHom M ((RingHom.id O).fromOpposite mul_comm)
  haveI : IsCentralScalar O M := ⟨fun _ _ => rfl⟩
  inferInstanceAs (CommRing (TrivSqZeroExt O M))

variable {O M}

def SqExt.mk (a : O) (m : M) : SqExt O M := (a, m)

def SqExt.fst (x : SqExt O M) : O := TrivSqZeroExt.fst x

def SqExt.snd (x : SqExt O M) : M := TrivSqZeroExt.snd x

namespace SqExt

omit [CommRing O] [AddCommGroup M] [Module O M] in
lemma ext {x y : SqExt O M} (h1 : x.fst = y.fst) (h2 : x.snd = y.snd) : x = y :=
  Prod.ext h1 h2

omit [CommRing O] [AddCommGroup M] [Module O M] in
@[simp] lemma fst_mk (a : O) (m : M) : (mk a m).fst = a := rfl
omit [CommRing O] [AddCommGroup M] [Module O M] in
@[simp] lemma snd_mk (a : O) (m : M) : (mk a m).snd = m := rfl
@[simp] lemma fst_add (x y : SqExt O M) : (x + y).fst = x.fst + y.fst := rfl
@[simp] lemma snd_add (x y : SqExt O M) : (x + y).snd = x.snd + y.snd := rfl
@[simp] lemma fst_zero : (0 : SqExt O M).fst = 0 := rfl
@[simp] lemma snd_zero : (0 : SqExt O M).snd = 0 := rfl
@[simp] lemma fst_one : (1 : SqExt O M).fst = 1 := rfl
@[simp] lemma snd_one : (1 : SqExt O M).snd = 0 := rfl
@[simp] lemma fst_mul (x y : SqExt O M) : (x * y).fst = x.fst * y.fst := rfl
@[simp] lemma snd_mul (x y : SqExt O M) : (x * y).snd = x.fst • y.snd + y.fst • x.snd := rfl

lemma isUnit_iff (x : SqExt O M) : IsUnit x ↔ IsUnit x.fst := by
  letI : Module Oᵐᵒᵖ M := Module.compHom M ((RingHom.id O).fromOpposite mul_comm)
  haveI : IsCentralScalar O M := ⟨fun _ _ => rfl⟩
  exact TrivSqZeroExt.isUnit_iff_isUnit_fst (R := O) (M := M)

def sndHom : SqExt O M →+ M := ⟨⟨snd, rfl⟩, fun _ _ => rfl⟩

def fstHom : SqExt O M →+* O where
  toFun := fst
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

def lift {A : Type} [CommRing A] (ε : A →+* O) (d : A →+ M)
    (hd : ∀ f f', d (f * f') = ε f • d f' + ε f' • d f) : A →+* SqExt O M :=
  letI : Module Oᵐᵒᵖ M := Module.compHom M ((RingHom.id O).fromOpposite mul_comm)
  haveI : IsCentralScalar O M := ⟨fun _ _ => rfl⟩
  GlobalTheory.SquareZeroLeibnizPoint.sqzOfLeibniz ε d hd

instance [IsLocalRing O] : IsLocalRing (SqExt O M) := by
  haveI : Nontrivial (SqExt O M) := (fstHom (O := O) (M := M)).domain_nontrivial
  refine IsLocalRing.of_isUnit_or_isUnit_of_isUnit_add ?_
  intro a b h
  rw [isUnit_iff, fst_add] at h
  rw [isUnit_iff, isUnit_iff]
  exact IsLocalRing.isUnit_or_isUnit_of_isUnit_add h

end SqExt

end Ring

section Alg

variable {R₀ : Type} [CommRing R₀] (O : LAlg R₀)
  (M : Type) [AddCommGroup M] [Module (O : Type) M]

lemma lhom_ext {R S : LAlg R₀} {f g : LHom R S} (h : ∀ a, f.1 a = g.1 a) : f = g :=
  Subtype.ext (AlgHom.ext h)

def sqAlg : LAlg R₀ :=
  letI : Algebra R₀ (SqExt (O : Type) M) :=
    (SqExt.lift (algebraMap R₀ (O : Type)) 0 (by simp)).toAlgebra
  { carrier := SqExt (O : Type) M }

def sqProj : LHom (sqAlg O M) O :=
  ⟨{ (SqExt.fstHom : SqExt (O : Type) M →+* O) with commutes' := fun _ => rfl },
    ⟨fun a h => (SqExt.isUnit_iff a).2 h⟩⟩

variable {O M}

def sqLift {A : LAlg R₀} (ε : LHom A O) (d : (A : Type) →+ M)
    (hd : ∀ f f', d (f * f') = ε.1 f • d f' + ε.1 f' • d f)
    (h0 : ∀ r, d (algebraMap R₀ (A : Type) r) = 0) : LHom A (sqAlg O M) :=
  ⟨{ (SqExt.lift (ε.1 : (A : Type) →+* O) d hd : (A : Type) →+* SqExt (O : Type) M) with
      commutes' := fun r => SqExt.ext (ε.1.commutes r) (h0 r) },
    ⟨fun a h => ε.2.map_nonunit a ((SqExt.isUnit_iff _).1 h)⟩⟩

variable (O M)

def sqIncl : LHom O (sqAlg O M) := sqLift (LHom.id O) 0 (by simp) (by simp)

lemma sqProj_sqZero : (sqProj O M).SqZero := by
  refine ⟨fun a => ⟨SqExt.mk a 0, rfl⟩, ?_⟩
  rw [pow_two, eq_bot_iff, Ideal.mul_le]
  intro r hr s hs
  have hr' : SqExt.fst (O := (O : Type)) (M := M) r = 0 := hr
  have hs' : SqExt.fst (O := (O : Type)) (M := M) s = 0 := hs
  rw [Ideal.mem_bot]
  refine SqExt.ext (O := (O : Type)) (M := M) ?_ ?_
  · exact (SqExt.fst_mul r s).trans (by rw [hr', zero_mul]; rfl)
  · exact (SqExt.snd_mul r s).trans (by rw [hr', hs', zero_smul, zero_smul, add_zero]; rfl)

lemma sqProj_comp_sqIncl : (sqProj O M).comp (sqIncl O M) = LHom.id O := lhom_ext fun _ => rfl

variable {O M}

def sqKer : M →+ (sqProj O M).ker where
  toFun m := ⟨SqExt.mk 0 m, rfl⟩
  map_zero' := rfl
  map_add' _ _ := Subtype.ext (SqExt.ext (O := (O : Type)) (M := M) (add_zero _).symm rfl)

lemma sqKer_injective : Function.Injective (sqKer : M → (sqProj O M).ker) := fun _ _ h =>
  congrArg (fun x : (sqProj O M).ker => SqExt.snd (O := (O : Type)) (M := M) x.1) h

lemma sqKer_surjective : Function.Surjective (sqKer : M → (sqProj O M).ker) := fun x =>
  ⟨SqExt.snd (O := (O : Type)) (M := M) x.1,
    Subtype.ext (SqExt.ext (O := (O : Type)) (M := M) (Eq.symm x.2) rfl)⟩

lemma smul_sqKer (r : R₀) (m : M) :
    r • (sqKer m : (sqProj O M).ker) = sqKer (algebraMap R₀ (O : Type) r • m) := by
  refine Subtype.ext ?_
  refine (Algebra.smul_def (A := (sqAlg O M : Type)) r _).trans ?_
  refine SqExt.ext (O := (O : Type)) (M := M) (mul_zero _) ?_
  refine (SqExt.snd_mul _ _).trans ?_
  change algebraMap R₀ (O : Type) r • m + (0 : (O : Type)) • (0 : M) = algebraMap R₀ (O : Type) r • m
  simp

variable {M' : Type} [AddCommGroup M'] [Module (O : Type) M']

def sqMap (u : M →ₗ[(O : Type)] M') : LHom (sqAlg O M) (sqAlg O M') :=
  sqLift (sqProj O M) (u.toAddMonoidHom.comp SqExt.sndHom)
    (fun f f' => by
      refine (congrArg u (SqExt.snd_mul (O := (O : Type)) (M := M) f f')).trans ?_
      rw [map_add, map_smul, map_smul]; rfl)
    (fun _ => map_zero u)

lemma map_sqMap_tg (B : BX R₀) {ι : Type} [Fintype ι] (w : ι → B.gg) (m : ι → M)
    (u : M →ₗ[(O : Type)] M') :
    B.map (sqMap u) (B.tg (sqProj O M) (sqProj_sqZero O M) (∑ k, w k ⊗ₜ[R₀] sqKer (m k))) =
      B.tg (sqProj O M') (sqProj_sqZero O M') (∑ k, w k ⊗ₜ[R₀] sqKer (u (m k))) := by
  rw [← B.tg_nat (sqProj O M) (sqProj O M') (sqProj_sqZero O M) (sqProj_sqZero O M') (sqMap u)
    (fun _ h => h), map_sum]
  rfl

end Alg

section Lie

variable {O : Type} [CommRing O] {p g : ℕ} {M : Type} [AddCommGroup M] [Module O M]

lemma lie_nsmul (x : LieDualModP p O g) : p • x = 0 := by
  obtain ⟨l, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  rw [← Nat.cast_smul_eq_nsmul O, ← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
  exact Submodule.smul_mem_smul (Ideal.mem_span_singleton_self _) trivial

def lieBasis (O : Type) [CommRing O] (p g : ℕ) (k : Fin g) : LieDualModP p O g :=
  Submodule.Quotient.mk (Pi.single k 1)

def lieLift (O : Type) [CommRing O] [Module O M] (m : Fin g → M) (hm : ∀ k, p • m k = 0) : LieDualModP p O g →ₗ[O] M :=
  Submodule.liftQ _ (Fintype.linearCombination O m) (by
    refine Submodule.smul_le.2 fun r hr l _ => ?_
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 hr
    rw [LinearMap.mem_ker, map_smul, mul_smul, Fintype.linearCombination_apply, Finset.smul_sum,
      Finset.sum_eq_zero, smul_zero]
    intro k _
    rw [smul_comm, Nat.cast_smul_eq_nsmul, hm, smul_zero])

lemma lieLift_mk (m : Fin g → M) (hm : ∀ k, p • m k = 0) (l : Fin g → O) :
    lieLift O m hm (Submodule.Quotient.mk l) = ∑ k, l k • m k :=
  Fintype.linearCombination_apply O m l

lemma lieLift_basis (m : Fin g → M) (hm : ∀ k, p • m k = 0) (k : Fin g) :
    lieLift O m hm (lieBasis O p g k) = m k := by
  rw [lieBasis, lieLift_mk, Finset.sum_eq_single k]
  · simp
  · intro j _ hj; simp [hj]
  · simp

lemma sum_lieBasis (l : Fin g → O) :
    ∑ k, l k • lieBasis O p g k = Submodule.Quotient.mk l := by
  have h : l = ∑ k, l k • (Pi.single k 1 : Fin g → O) := by
    ext j; simp [Finset.sum_apply, Pi.single_apply]
  conv_rhs => rw [h]
  rw [← Submodule.mkQ_apply, map_sum]
  rfl

lemma lie_ext {u u' : LieDualModP p O g →ₗ[O] M}
    (h : ∀ k, u (lieBasis O p g k) = u' (lieBasis O p g k)) : u = u' := by
  refine LinearMap.ext fun x => ?_
  obtain ⟨l, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  rw [← sum_lieBasis, map_sum, map_sum]
  simp only [map_smul, h]

end Lie

section Core

variable {R₀ : Type} [CommRing R₀] {B : BX R₀} {O A : LAlg R₀} {p g : ℕ}
  {sO : LHom O A} {ε : LHom A O} {y : B.G A} {w : Fin g → B.gg}

abbrev tgPt (B : BX R₀) (O : LAlg R₀) (w : Fin g → B.gg) {M : Type} [AddCommGroup M]
    [Module (O : Type) M] (m : Fin g → M) : B.G (sqAlg O M) :=
  B.tg (sqProj O M) (sqProj_sqZero O M) (∑ k, w k ⊗ₜ[R₀] sqKer (m k))

variable {M : Type} [AddCommGroup M] [Module (O : Type) M]

lemma snd_smul (φ : LHom A (sqAlg O M)) (h1 : φ.comp sO = sqIncl O M) (o : (O : Type))
    (f : (A : Type)) :
    SqExt.snd (O := (O : Type)) (M := M) (φ.1 (sO.1 o * f)) =
      o • SqExt.snd (O := (O : Type)) (M := M) (φ.1 f) := by
  have h : φ.1 (sO.1 o) = SqExt.mk (M := M) o 0 := congrArg (fun ψ => ψ.1 o) h1
  rw [map_mul, h]
  refine (SqExt.snd_mul (O := (O : Type)) (M := M) _ _).trans ?_
  simp

lemma snd_leibniz (φ : LHom A (sqAlg O M)) (h2 : (sqProj O M).comp φ = ε) (f f' : (A : Type)) :
    SqExt.snd (O := (O : Type)) (M := M) (φ.1 (f * f')) =
      ε.1 f • SqExt.snd (O := (O : Type)) (M := M) (φ.1 f') +
        ε.1 f' • SqExt.snd (O := (O : Type)) (M := M) (φ.1 f) := by
  rw [map_mul, ← h2]
  exact SqExt.snd_mul (O := (O : Type)) (M := M) _ _

lemma exists_lift (hε : ε.comp sO = LHom.id O) (d : (A : Type) →+ M)
    (h1 : ∀ o f, d (sO.1 o * f) = o • d f)
    (h2 : ∀ f f', d (f * f') = ε.1 f • d f' + ε.1 f' • d f) :
    ∃ φ : LHom A (sqAlg O M), φ.comp sO = sqIncl O M ∧ (sqProj O M).comp φ = ε ∧
      ∀ f, SqExt.snd (O := (O : Type)) (M := M) (φ.1 f) = d f := by
  have d1 : d 1 = 0 := by
    have h := h2 1 1
    simp only [mul_one, map_one, one_smul] at h
    simpa using h
  have dO : ∀ o, d (sO.1 o) = 0 := fun o => by
    have h := h1 o 1
    rwa [mul_one, d1, smul_zero] at h
  refine ⟨sqLift ε d h2 (fun r => by rw [← sO.1.commutes, dO]), lhom_ext fun o => ?_,
    lhom_ext fun _ => rfl, fun _ => rfl⟩
  exact SqExt.ext (O := (O : Type)) (M := M) (congrArg (fun ψ => ψ.1 o) hε) (dO o)

variable {M' : Type} [AddCommGroup M'] [Module (O : Type) M']

lemma sqMap_comp_sO (φ : LHom A (sqAlg O M)) (h1 : φ.comp sO = sqIncl O M)
    (u : M →ₗ[(O : Type)] M') : ((sqMap u).comp φ).comp sO = sqIncl O M' :=
  lhom_ext fun o => by
    have h : φ.1 (sO.1 o) = SqExt.mk (M := M) o 0 := congrArg (fun ψ => ψ.1 o) h1
    change (sqMap u).1 (φ.1 (sO.1 o)) = _
    rw [h]
    exact SqExt.ext (O := (O : Type)) (M := M') rfl (map_zero u)

lemma sqProj_comp_sqMap (φ : LHom A (sqAlg O M)) (h2 : (sqProj O M).comp φ = ε)
    (u : M →ₗ[(O : Type)] M') : (sqProj O M').comp ((sqMap u).comp φ) = ε := by
  rw [← h2]; exact lhom_ext fun _ => rfl

lemma tg_act {E : Type} [CommRing E] (Ac : OAct B O p E) (a : E) (gb : Module.Basis (Fin g) R₀ B.gg)
    (m : Fin g → M) (hm : ∀ k, p • m k = 0) (x : torP B p (sqAlg O M))
    (hx : (x : B.G (sqAlg O M)) = tgPt B O gb m) :
    (Ac.act a (sqAlg O M) (sqIncl O M) x : B.G (sqAlg O M)) =
      tgPt B O gb fun k' => ∑ k, algebraMap R₀ (O : Type) (gb.repr (Ac.actL a (gb k)) k') • m k := by
  have hk : ∀ k, p • (sqKer (m k) : (sqProj O M).ker) = 0 := fun k => by
    rw [← map_nsmul, hm, map_zero]
  have hx' : x = ∑ k, (⟨B.tg (sqProj O M) (sqProj_sqZero O M) (gb k ⊗ₜ[R₀] sqKer (m k)),
      tg_torP B p _ _ _ _ (hk k)⟩ : torP B p (sqAlg O M)) := by
    refine Subtype.ext ?_
    rw [hx, AddSubmonoidClass.coe_finset_sum, tgPt, map_sum]
  rw [hx', map_sum, AddSubmonoidClass.coe_finset_sum]
  simp only [Ac.act_tg a (sqIncl O M) (sqProj O M) (sqProj_sqZero O M) _ _ (hk _)]
  rw [← map_sum, tgPt]
  congr 1
  simp only [map_sum, TensorProduct.tmul_sum, ← smul_sqKer, ← TensorProduct.smul_tmul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [← TensorProduct.sum_tmul, gb.sum_repr]

end Core

theorem universal_derivation :
  (∀ {R₀ : Type} [CommRing R₀] {p : ℕ} [Fact p.Prime] {g : ℕ} {B : BX R₀} {Tw : ATowerL R₀ p} {Dt : DualTower Tw} [Algebra ℤ_[p] (Tw.O : Type)] {Oe : Type} [CommRing Oe] [Algebra ℤ_[p] Oe] {σ : Oe ≃ₐ[ℤ_[p]] Oe} {cp : (Tw.O : Type)} (D : Dat p g B Tw Dt Oe σ cp), ∀ (S : LAlg R₀) (s : LHom Tw.O S) (π : LHom S Tw.O) (hπ : π.SqZero), π.comp s = LHom.id Tw.O →
    (∀ m : Fin g → π.ker, (∀ k, p • m k = 0) → ∃! φ : LHom (D.fin.AAx (D.ptIdx 0)) S, φ.comp (D.fin.sO (D.ptIdx 0)) = s ∧ π.comp φ = (D.ptMap 0) ∧
      B.map φ (D.fin.y (D.ptIdx 0)) = B.tg π hπ (∑ k, D.ch.gb k ⊗ₜ[R₀] m k)) ∧
    (∀ φ : LHom (D.fin.AAx (D.ptIdx 0)) S, φ.comp (D.fin.sO (D.ptIdx 0)) = s → π.comp φ = (D.ptMap 0) → ∃! m : Fin g → π.ker, (∀ k, p • m k = 0) ∧
      B.map φ (D.fin.y (D.ptIdx 0)) = B.tg π hπ (∑ k, D.ch.gb k ⊗ₜ[R₀] m k))) →
  (∀ {R₀ : Type} [CommRing R₀] {p : ℕ} [Fact p.Prime] {g : ℕ} {B : BX R₀} {Tw : ATowerL R₀ p} {Dt : DualTower Tw} [Algebra ℤ_[p] (Tw.O : Type)] {Oe : Type} [CommRing Oe] [Algebra ℤ_[p] Oe] {σ : Oe ≃ₐ[ℤ_[p]] Oe} {cp : (Tw.O : Type)} (D : Dat p g B Tw Dt Oe σ cp), ∃ δ : ((D.fin.AAx (D.ptIdx 0)) : Type) →+ LieDualModP p (Tw.O : Type) g,
    (∀ o f, δ ((D.fin.sO (D.ptIdx 0)).1 o * f) = o • δ f) ∧ (∀ f f', δ (f * f') = (D.ptMap 0).1 f • δ f' + (D.ptMap 0).1 f' • δ f) ∧
    (∀ (M : Type) [AddCommGroup M] [Module (Tw.O : Type) M] (d : ((D.fin.AAx (D.ptIdx 0)) : Type) →+ M),
      (∀ o f, d ((D.fin.sO (D.ptIdx 0)).1 o * f) = o • d f) → (∀ f f', d (f * f') = (D.ptMap 0).1 f • d f' + (D.ptMap 0).1 f' • d f) →
      ∃! u : LieDualModP p (Tw.O : Type) g →ₗ[(Tw.O : Type)] M, ∀ f, d f = u (δ f)) ∧
    ∀ (a : Oe) (α : LHom (D.fin.AAx (D.ptIdx 0)) (D.fin.AAx (D.ptIdx 0))), α.comp (D.fin.sO (D.ptIdx 0)) = (D.fin.sO (D.ptIdx 0)) →
      B.map α (D.fin.y (D.ptIdx 0)) = (D.A.act a (D.fin.AAx (D.ptIdx 0)) (D.fin.sO (D.ptIdx 0)) ⟨(D.fin.y (D.ptIdx 0)), (mem_torP B p _).2 (D.fin.y_p _)⟩ : B.G (D.fin.AAx (D.ptIdx 0))) →
      ∀ f (l : Fin g → (Tw.O : Type)), δ f = Submodule.Quotient.mk l → δ (α.1 f) = Submodule.Quotient.mk ((D.H.ρL a)ᵀ *ᵥ l)) := by
  intro hyp R₀ _ p _ g B Tw Dt _ Oe _ _ σ cp D
  obtain ⟨hε, hy, huniq⟩ := Classical.choose_spec (Classical.choose_spec
    (D.fin.univ Tw.O (LHom.id Tw.O) (ptOf B D.L.τ 0) (D.pt_p 0)))
  change (D.ptMap 0).comp (D.fin.sO (D.ptIdx 0)) = _ at hε
  have huniq' : ∀ φ' : LHom (D.fin.AAx (D.ptIdx 0)) Tw.O,
      φ'.comp (D.fin.sO (D.ptIdx 0)) = LHom.id Tw.O → B.map φ' (D.fin.y (D.ptIdx 0)) = 0 →
        φ' = D.ptMap 0 := fun φ' h1 h2 =>
    eq_of_heq (huniq (D.ptIdx 0) φ' h1 (h2.trans (by simp [ptOf]))).2
  have H1 : ∀ (M : Type) [AddCommGroup M] [Module (Tw.O : Type) M] (m : Fin g → M),
      (∀ k, p • m k = 0) → ∃! φ : LHom (D.fin.AAx (D.ptIdx 0)) (sqAlg Tw.O M),
        φ.comp (D.fin.sO (D.ptIdx 0)) = sqIncl Tw.O M ∧ (sqProj Tw.O M).comp φ = D.ptMap 0 ∧
          B.map φ (D.fin.y (D.ptIdx 0)) = tgPt B Tw.O D.ch.gb m := fun M _ _ m hm =>
    (hyp D _ _ _ (sqProj_sqZero Tw.O M) (sqProj_comp_sqIncl Tw.O M)).1 (fun k => sqKer (m k))
      (fun k => by rw [← map_nsmul, hm, map_zero])
  have H2 : ∀ (M : Type) [AddCommGroup M] [Module (Tw.O : Type) M]
      (φ : LHom (D.fin.AAx (D.ptIdx 0)) (sqAlg Tw.O M)),
      φ.comp (D.fin.sO (D.ptIdx 0)) = sqIncl Tw.O M → (sqProj Tw.O M).comp φ = D.ptMap 0 →
      ∃! m : Fin g → M, (∀ k, p • m k = 0) ∧
        B.map φ (D.fin.y (D.ptIdx 0)) = tgPt B Tw.O D.ch.gb m := by
    intro M _ _ φ h1 h2
    obtain ⟨m, ⟨hm1, hm2⟩, hm3⟩ :=
      (hyp D _ _ _ (sqProj_sqZero Tw.O M) (sqProj_comp_sqIncl Tw.O M)).2 φ h1 h2
    choose n hn using fun k => sqKer_surjective (O := Tw.O) (M := M) (m k)
    obtain rfl : m = fun k => sqKer (n k) := funext fun k => (hn k).symm
    refine ⟨n, ⟨fun k => sqKer_injective (O := Tw.O) (M := M) ?_, hm2⟩, fun n' hn' => ?_⟩
    · rw [map_nsmul, map_zero]; exact hm1 k
    · have h := hm3 (fun k => sqKer (n' k))
        ⟨fun k => by rw [← map_nsmul, hn'.1, map_zero], hn'.2⟩
      exact funext fun k => sqKer_injective (O := Tw.O) (M := M) (congrFun h k)
  obtain ⟨φ₀, ⟨h1, h2, h3⟩, -⟩ := H1 _ (lieBasis (Tw.O : Type) p g) fun k => lie_nsmul _
  have key : ∀ (M : Type) [AddCommGroup M] [Module (Tw.O : Type) M]
      (u : LieDualModP p (Tw.O : Type) g →ₗ[(Tw.O : Type)] M),
      B.map ((sqMap u).comp φ₀) (D.fin.y (D.ptIdx 0)) =
        tgPt B Tw.O D.ch.gb fun k => u (lieBasis (Tw.O : Type) p g k) := by
    intro M _ _ u
    rw [B.map_comp, h3]
    exact map_sqMap_tg B _ _ u
  have key2 : ∀ (M : Type) [AddCommGroup M] [Module (Tw.O : Type) M] (m : Fin g → M)
      (hm : ∀ k, p • m k = 0) (φ : LHom (D.fin.AAx (D.ptIdx 0)) (sqAlg Tw.O M)),
      φ.comp (D.fin.sO (D.ptIdx 0)) = sqIncl Tw.O M → (sqProj Tw.O M).comp φ = D.ptMap 0 →
      B.map φ (D.fin.y (D.ptIdx 0)) = tgPt B Tw.O D.ch.gb m →
      φ = (sqMap (lieLift (Tw.O : Type) m hm)).comp φ₀ := by
    intro M _ _ m hm φ k1 k2 k3
    refine (H1 M m hm).unique ⟨k1, k2, k3⟩
      ⟨sqMap_comp_sO φ₀ h1 _, sqProj_comp_sqMap φ₀ h2 _, ?_⟩
    rw [key]
    simp only [lieLift_basis]
  refine ⟨(SqExt.sndHom (O := (Tw.O : Type)) (M := LieDualModP p (Tw.O : Type) g)).comp
    (φ₀.1.toRingHom.toAddMonoidHom), snd_smul φ₀ h1, snd_leibniz φ₀ h2, ?_, ?_⟩
  · intro M _ _ d d1 d2
    obtain ⟨φ, k1, k2, k3⟩ := exists_lift hε d d1 d2
    obtain ⟨m, ⟨hm1, hm2⟩, hm3⟩ := H2 M φ k1 k2
    refine ⟨lieLift (Tw.O : Type) m hm1, fun f => ?_, fun u hu => lie_ext fun k => ?_⟩
    · rw [← k3, key2 M m hm1 φ k1 k2 hm2]; rfl
    · have hφ : φ = (sqMap u).comp φ₀ := lhom_ext fun f =>
        SqExt.ext (O := (Tw.O : Type)) (M := M)
          (congrArg (fun ψ => ψ.1 f) (k2.trans h2.symm)) ((k3 f).trans (hu f))
      have h := hm3 (fun k => u (lieBasis (Tw.O : Type) p g k))
        ⟨fun k => by rw [← map_nsmul, lie_nsmul, map_zero], by rw [hφ, key]⟩
      rw [lieLift_basis]
      exact congrFun h k
  · intro a α hα1 hα2 f l hl
    have k1 : (φ₀.comp α).comp (D.fin.sO (D.ptIdx 0)) = sqIncl Tw.O _ := by
      rw [← h1]
      exact congrArg φ₀.comp hα1
    have k3 : B.map (φ₀.comp α) (D.fin.y (D.ptIdx 0)) = tgPt B Tw.O D.ch.gb
        fun k => (Submodule.Quotient.mk (D.H.ρL a k) : LieDualModP p (Tw.O : Type) g) := by
      rw [B.map_comp, hα2, D.A.act_nat a _ _ φ₀ h1,
        tg_act D.A a D.ch.gb (lieBasis (Tw.O : Type) p g) (fun k => lie_nsmul _) _ h3]
      simp only [← D.L.ρL_spec, sum_lieBasis]
    have k2 : (sqProj Tw.O _).comp (φ₀.comp α) = D.ptMap 0 := by
      refine huniq' _ ?_ ?_
      · exact (congrArg (sqProj Tw.O _).comp k1).trans (sqProj_comp_sqIncl Tw.O _)
      · rw [B.map_comp, k3]
        exact (B.tg_ker _ _ _).2 ⟨_, rfl⟩
    have h := congrArg (fun ψ => SqExt.snd (O := (Tw.O : Type))
      (M := LieDualModP p (Tw.O : Type) g) (ψ.1 f)) (key2 _ _ (fun k => lie_nsmul _) _ k1 k2 k3)
    refine h.trans ?_
    refine (congrArg (fun x => lieLift (Tw.O : Type)
      (fun k => (Submodule.Quotient.mk (D.H.ρL a k) : LieDualModP p (Tw.O : Type) g))
      (fun k => lie_nsmul _) x) hl).trans ?_
    rw [lieLift_mk]
    have hρ : (D.H.ρL a)ᵀ *ᵥ l = ∑ k, l k • D.H.ρL a k := by
      ext j
      simp [Matrix.mulVec, dotProduct, Finset.sum_apply, mul_comm]
    rw [hρ, ← Submodule.mkQ_apply, map_sum]
    rfl

end GlobalTheory.CotUniv

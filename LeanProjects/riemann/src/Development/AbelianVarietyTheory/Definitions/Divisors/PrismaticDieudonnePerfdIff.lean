import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PrismaticDieudonnePerfd
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.InjectiveOfSmulMemRange
import Development.AbelianVarietyTheory.Definitions.Divisors.PadicActionConstInjective

set_option autoImplicit false

noncomputable section

open CategoryTheory WittVector Ideal

namespace GlobalTheory.PerfdLat

open GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.Published

structure PrismData (p : ℕ) [Fact p.Prime] : Type 1 where

  M : ∀ S : CycPerfd p, PDivGroup p S.R → ModuleCat.{0} (Ainf p S.R)

  map : ∀ (S : CycPerfd p) (G H : PDivGroup p S.R), (G ⟶ H) →+ (M S H →ₗ[Ainf p S.R] M S G)

  φ : ∀ (S : CycPerfd p) (G : PDivGroup p S.R), M S G →ₛₗ[(frobenius : Ainf p S.R →+* Ainf p S.R)] M S G

  lie : ∀ (S : CycPerfd p) (G : PDivGroup p S.R), M S G →ₛₗ[fontaineTheta S.R p] G.dual.Lie

  du : ∀ (S : CycPerfd p) (G : PDivGroup p S.R), M S G.dual ≃ₗ[Ainf p S.R] Module.Dual (Ainf p S.R) (M S G)

  l : ∀ S : CycPerfd p, M S (PDivGroup.mu p S.R)

  e : ∀ S : CycPerfd p, M S (const p S.R)

  projective : ∀ S G, Module.Projective (Ainf p S.R) (M S G)

  finite : ∀ S G, Module.Finite (Ainf p S.R) (M S G)

  rank_eq : ∀ S G q, Module.rankAtStalk (R := Ainf p S.R) (M S G) q = G.height

  exists_φ_eq : ∀ S G m, ∃ n, φ S G n = frobenius (xi S.ε) • m

  lie_projective : ∀ (S : CycPerfd p) (G : PDivGroup p S.R), Module.Projective S.R G.dual.Lie

  lie_finite : ∀ (S : CycPerfd p) (G : PDivGroup p S.R), Module.Finite S.R G.dual.Lie

  lie_surjective : ∀ S G, Function.Surjective (lie S G)

  lie_eq_zero_iff : ∀ S G m, lie S G m = 0 ↔ ∃ n, φ S G m = frobenius (xi S.ε) • n

  map_id : ∀ S G, map S G G (𝟙 G) = LinearMap.id

  map_comp : ∀ S G H K (f : G ⟶ H) (g : H ⟶ K), map S G K (f ≫ g) = map S G H f ∘ₗ map S H K g

  map_φ : ∀ S G H (f : G ⟶ H) (m : M S H), map S G H f (φ S H m) = φ S G (map S G H f m)

  lie_map : ∀ S G H (f : G ⟶ H) (m : M S H),
    lie S G (map S G H f m) = lieMap H.dual G.dual (dualHom G H f) (lie S H m)

  du_map : ∀ S G H (f : G ⟶ H) (m : M S H) (x : M S G.dual),
    du S H (map S H.dual G.dual (dualHom G H f) x) m = du S G x (map S G H f m)

  l_bijective : ∀ S, Function.Bijective (LinearMap.toSpanSingleton (Ainf p S.R) _ (l S))

  e_bijective : ∀ S, Function.Bijective (LinearMap.toSpanSingleton (Ainf p S.R) _ (e S))

  φ_l : ∀ S, φ S _ (l S) = frobenius (xi S.ε) • l S

  φ_e : ∀ S, φ S _ (e S) = e S

  map_eps : ∀ S, map S _ _ (epsHom (zeta S.ε) S.zeta_zero (zeta_succ_pow S.ε)) (l S) = Sandwich.mu S.ε • e S

  du_e_l : ∀ S, du S (PDivGroup.mu p S.R) (e S) (l S) = 1

  baseChange : ∀ (S S' : CycPerfd p) [Algebra S.R S'.R] (α : Ainf p S.R →+* Ainf p S'.R), S.Over S' α →
    ∃ bc : ∀ G : PDivGroup p S.R, M S G →ₛₗ[α] M S' (G.baseChange S'.R),
      (∀ G, Submodule.span (Ainf p S'.R) (Set.range (bc G)) = ⊤ ∧ ∀ m, bc G (φ S G m) = φ S' _ (bc G m)) ∧
      (∀ (G H : PDivGroup p S.R) (f : G ⟶ H) (m : M S H),
        bc G (map S G H f m) = map S' _ _ (baseChangeMap S'.R f) (bc H m)) ∧
      ∀ j : PDivGroup.mu p S'.R ⟶ (PDivGroup.mu p S.R).baseChange S'.R,
        (∀ n, j.app n (1 ⊗ₜ AddMonoidAlgebra.single 1 1) = AddMonoidAlgebra.single 1 1) →
          map S' _ _ j (bc _ (l S)) = l S'

attribute [instance] PrismData.projective PrismData.finite

theorem PrismData.nonempty (h : PrismaticDieudonnePerfd) (p : ℕ) [Fact p.Prime] : Nonempty (PrismData p) := by
  obtain ⟨M, map, φ, lie, du, l, e, h1, h2, h3, h4, h5⟩ := h p
  exact ⟨⟨M, map, φ, lie, du, l, e, fun S G => (h1 S G).1, fun S G => (h1 S G).2.1, fun S G => (h1 S G).2.2.1,
    fun S G => (h1 S G).2.2.2.1, fun S G => (h1 S G).2.2.2.2.1, fun S G => (h1 S G).2.2.2.2.2.1,
    fun S G => (h1 S G).2.2.2.2.2.2.1, fun S G => (h1 S G).2.2.2.2.2.2.2.1, fun S G => (h1 S G).2.2.2.2.2.2.2.2, h2,
    fun S G H f m => (h3 S G H f m).1, fun S G H f m => (h3 S G H f m).2.1, fun S G H f m => (h3 S G H f m).2.2,
    fun S => (h4 S).1, fun S => (h4 S).2.1, fun S => (h4 S).2.2.1, fun S => (h4 S).2.2.2.1,
    fun S => (h4 S).2.2.2.2.1, fun S => (h4 S).2.2.2.2.2, h5⟩⟩

theorem prismaticDieudonnePerfd_iff :
    PrismaticDieudonnePerfd ↔ ∀ (p : ℕ) [Fact p.Prime], Nonempty (PrismData p) :=
  ⟨PrismData.nonempty, fun h p _ => (h p).elim fun D => ⟨D.M, D.map, D.φ, D.lie, D.du, D.l, D.e,
    fun S G => ⟨D.projective S G, D.finite S G, D.rank_eq S G, D.exists_φ_eq S G, D.lie_projective S G,
      D.lie_finite S G, D.lie_surjective S G, D.lie_eq_zero_iff S G, D.map_id S G⟩, D.map_comp,
    fun S G H f m => ⟨D.map_φ S G H f m, D.lie_map S G H f m, D.du_map S G H f m⟩,
    fun S => ⟨D.l_bijective S, D.e_bijective S, D.φ_l S, D.φ_e S, D.map_eps S, D.du_e_l S⟩, D.baseChange⟩⟩

section Const

variable {p : ℕ} [Fact p.Prime] {O : Type} [CommRing O]

structure ConstTate (ε : (PDivGroup.mu p O).Tate) (G : PDivGroup p O) : Type where

  t : Fin G.height → G.Tate

  t' : Fin G.height → G.dual.Tate

  pair : ∀ i j, pairing G O (t i) (t' j) = if i = j then ε else 0

theorem pairing_bidual (G : PDivGroup p O) (t : G.Tate) (χ : G.dual.Tate) :
    pairing G.dual O χ (tateCongr O G.bidual t) = pairing G O t χ :=
  muRoot_ext fun n => by
    rw [muRoot_pairing, muRoot_pairing, ← charHom_app_muT]
    change χ.pt n ((dualChar G t).app n _) = _
    rw [dualChar_app_muT, ← apply_charElem]
    rfl

theorem constHom_comp_dualChar (G : PDivGroup p O) (t : G.Tate) (χ : G.dual.Tate) :
    constHom G.dual χ ≫ dualChar G t = constHom (PDivGroup.mu p O) (pairing G O t χ) := by
  rw [← pairing_bidual]
  exact constHom_comp_charHom χ _

theorem dualHom_charHom (G : PDivGroup p O) (χ : G.dual.Tate) :
    dualHom G (PDivGroup.mu p O) (charHom G χ) = constHom G.dual χ := by
  rw [← LinearEquiv.symm_apply_eq, constHom_symm_apply]
  apply (charHom G).injective
  rw [charHom_tateMap, charHom_constGen, Category.comp_id]

section BaseChange

variable (O' : Type) [CommRing O'] [Algebra O O'] {G : PDivGroup p O}

theorem baseChange_mulP (G : PDivGroup p O) (n : ℕ) : (G.baseChange O').mulP n = PDiv.bcMap O' (G.mulP n) :=
  PDiv.bc_hom_ext fun a => by
    obtain ⟨b, rfl⟩ := G.res_surjective n a
    have h := map_nsmul (AddMonoidHom.mk' (baseChangeMap (G := G) (H := G) O') (baseChangeMap_add O')) p (𝟙 G)
    rw [← Nat.cast_smul_eq_nsmul ℤ_[p], ← Nat.cast_smul_eq_nsmul ℤ_[p]] at h
    have h1 : baseChangeMap O' ((p : ℤ_[p]) • 𝟙 G) = (p : ℤ_[p]) • 𝟙 (G.baseChange O') :=
      h.trans (congrArg _ ((baseChangeFunctor p O O').map_id G))
    have h2 := congrArg (fun f => Hom.app f (n + 1) (1 ⊗ₜ b)) h1
    simp only [baseChangeMap_app, natCast_smul_id_app] at h2
    rw [PDiv.bcMap_tmul, mulP_res]
    exact ((G.baseChange O').mulP_res n (1 ⊗ₜ b)).trans h2.symm

def bcTate (t : G.Tate) : (G.baseChange O').Tate :=
  ⟨fun n => Algebra.TensorProduct.lift (AlgHom.id O' O') ((Algebra.ofId O O').comp (t.pt n)) fun _ _ => .all _ _,
    fun n => Algebra.TensorProduct.ext (Subsingleton.elim _ _) (AlgHom.ext fun a => by
      rw [baseChange_mulP]
      simp [t.pt_mulP])⟩

@[simp] theorem bcTate_pt (t : G.Tate) (n : ℕ) (r : O') (a : G.A n) :
    (bcTate O' t).pt n (r ⊗ₜ a) = r * algebraMap O O' (t.pt n a) := rfl

omit [Fact p.Prime] in

theorem isGroupLikeElem_one_tmul (χ : G.dual.Tate) (n : ℕ) :
    IsGroupLikeElem O' ((1 : O') ⊗ₜ[O] charElem χ n) where
  counit_eq_one := by simp [(isGroupLikeElem_charElem χ n).counit_eq_one]
  comul_eq_tmul_self := by
    simp [TensorProduct.comul_tmul, (isGroupLikeElem_charElem χ n).comul_eq_tmul_self]

def bcChar (χ : G.dual.Tate) : (G.baseChange O').dual.Tate :=
  ⟨fun n => evalPoint _ (isGroupLikeElem_one_tmul O' χ n), fun n => AlgHom.ext fun φ => by
    change ((G.baseChange O').dual.mulP n φ) ((1 : O') ⊗ₜ[O] charElem χ (n + 1)) = φ.ofConv (1 ⊗ₜ charElem χ n)
    rw [dual_mulP, CartierDual.map_apply, ← res_charElem χ n]
    rfl⟩

@[simp] theorem charElem_bcChar (χ : G.dual.Tate) (n : ℕ) : charElem (bcChar O' χ) n = 1 ⊗ₜ charElem χ n :=
  CartierDual.eq_of_forall_apply (R := O') fun φ => apply_charElem _ n φ

theorem muRoot_pairing_bc (t : G.Tate) (χ : G.dual.Tate) (n : ℕ) :
    muRoot (pairing _ O' (bcTate O' t) (bcChar O' χ)) n = algebraMap O O' (muRoot (pairing G O t χ) n) := by
  rw [muRoot_pairing, muRoot_pairing, charElem_bcChar, bcTate_pt, one_mul]

theorem tateMap_bcTate {H : PDivGroup p O} (f : G ⟶ H) (t : G.Tate) :
    tateMap _ _ O' (baseChangeMap O' f) (bcTate O' t) = bcTate O' (tateMap G H O f t) :=
  TateOver.ext (funext fun _ => Algebra.TensorProduct.ext (Subsingleton.elim _ _) (AlgHom.ext fun _ => rfl))

theorem dlog_bcChar (χ : G.dual.Tate) : dlog _ (bcChar O' χ) = (G.toBase O').omega (dlog G χ) :=
  Subtype.ext (funext fun n => by
    rw [dlog_val, charElem_bcChar, SemiHom.omega_val, dlog_val, PDiv.SemiBialgHom.cot_d, toBase_app])

def dualBaseChange (G : PDivGroup p O) : (G.baseChange O').dual ≅ G.dual.baseChange O' where
  hom := ⟨fun n => CartierDual.baseChangeHom O O' (G.A n), fun n => BialgHom.ext fun x => by
    change CartierDual.map ((G.baseChange O').mulP n) _ = _
    rw [baseChange_mulP]
    exact (CartierDual.baseChange_map O' (G.mulP n) x).symm⟩
  inv := ⟨fun n => (CartierDual.baseChange O O' (G.A n)).symm, fun n => BialgHom.ext fun x => by
    obtain ⟨y, rfl⟩ := (CartierDual.baseChange O O' (G.A (n + 1))).surjective x
    change PDiv.bcMap O' (CartierDual.map (G.mulP n)) ((CartierDual.baseChange O O' (G.A (n + 1))).symm
      (CartierDual.baseChange O O' (G.A (n + 1)) y)) = (CartierDual.baseChange O O' (G.A n)).symm
        (CartierDual.map ((G.baseChange O').mulP n) (CartierDual.baseChange O O' (G.A (n + 1)) y))
    rw [baseChange_mulP, PDiv.bcMap, PDiv.bcMap, ← CartierDual.baseChange_map, BialgEquiv.symm_apply_apply,
      BialgEquiv.symm_apply_apply]⟩
  hom_inv_id := hom_ext fun n => BialgHom.ext fun a => (CartierDual.baseChange O O' (G.A n)).apply_symm_apply a
  inv_hom_id := hom_ext fun n => BialgHom.ext fun a => (CartierDual.baseChange O O' (G.A n)).symm_apply_apply a

theorem tateMap_dualBaseChange (χ : G.dual.Tate) :
    tateMap _ _ O' (dualBaseChange O' G).hom (bcChar O' χ) = bcTate O' χ :=
  TateOver.ext (funext fun n => Algebra.TensorProduct.ext (Subsingleton.elim _ _) (AlgHom.ext fun φ => by
    change CartierDual.baseChange O O' (G.A n) (1 ⊗ₜ φ) (1 ⊗ₜ charElem χ n) = 1 * algebraMap O O' (χ.pt n φ)
    rw [CartierDual.baseChange_tmul_tmul, apply_charElem, one_mul, one_mul, Algebra.algebraMap_eq_smul_one]))

end BaseChange

namespace ConstTate

variable {ε : (PDivGroup.mu p O).Tate} {G : PDivGroup p O}

def ofPerfect (t : Fin G.height → G.Tate) (t' : Fin G.height → G.dual.Tate) (P : GL (Fin G.height) ℤ_[p])
    (h : ∀ i j, pairing G O (t i) (t' j) = P i j • ε) : ConstTate ε G where
  t := t
  t' j := ∑ k, P⁻¹ k j • t' k
  pair i j := by
    have h1 : ∑ k, P i k * P⁻¹ k j = if i = j then 1 else 0 := by
      have h2 := congrFun (congrFun P.mul_inv i) j
      rwa [Matrix.mul_apply, Matrix.one_apply] at h2
    simp only [map_sum, map_smul, h, smul_smul, mul_comm (P⁻¹ _ j)]
    rw [← Finset.sum_smul, h1]
    split_ifs <;> simp

variable (c : ConstTate ε G)

theorem constHom_comp (i j : Fin G.height) : constHom G (c.t i) ≫ charHom G (c.t' j) =
    if i = j then constHom (PDivGroup.mu p O) ε else 0 := by
  rw [constHom_comp_charHom, c.pair]
  split_ifs <;> simp

def dual : ConstTate ε G.dual where
  t := c.t'
  t' i := tateCongr O G.bidual (c.t i)
  pair j i := by rw [pairing_bidual, c.pair]; simp only [eq_comm]

def ofIso {H : PDivGroup p O} (e : G ≅ H) (h : H.height = G.height) : ConstTate ε H where
  t i := tateMap G H O e.hom (c.t (Fin.cast h i))
  t' j := tateMap _ _ O (dualHom H G e.inv) (c.t' (Fin.cast h j))
  pair i j := by
    rw [pairing_tateMap, ← tateMap_comp, ← dualHom_comp, e.hom_inv_id, dualHom_id, tateMap_id, c.pair]
    simp only [Fin.cast_inj]

def toTate : (Fin G.height → ℤ_[p]) →ₗ[ℤ_[p]] G.Tate := Fintype.linearCombination ℤ_[p] c.t

theorem pairing_toTate (x : Fin G.height → ℤ_[p]) (j : Fin G.height) :
    pairing G O (c.toTate x) (c.t' j) = x j • ε := by
  simp [toTate, Fintype.linearCombination_apply, LinearMap.sum_apply, c.pair]

theorem toTate_injective (hε : ∀ a : ℤ_[p], a • ε = 0 → a = 0) : Function.Injective c.toTate :=
  (injective_iff_map_eq_zero _).2 fun x hx => funext fun j => hε _ <| by
    rw [← c.pairing_toTate, hx, map_zero, LinearMap.zero_apply]

def Stable (f : End G) (ρ : Matrix (Fin G.height) (Fin G.height) ℤ_[p]) : Prop :=
  ∀ i, tateMap G G O f (c.t i) = ∑ k, ρ k i • c.t k

theorem stable_iff (f : End G) (ρ : Matrix (Fin G.height) (Fin G.height) ℤ_[p]) :
    c.Stable f ρ ↔ ∀ x, tateMap G G O f (c.toTate x) = c.toTate (ρ.mulVec x) := by
  constructor
  · intro h x
    simp only [toTate, Fintype.linearCombination_apply, map_sum, map_smul, h _, Finset.smul_sum, smul_smul,
      Matrix.mulVec, dotProduct, Finset.sum_smul]
    rw [Finset.sum_comm]
    simp only [mul_comm]
  · intro h i
    simpa [toTate, Fintype.linearCombination_apply, Pi.single_apply] using h (Pi.single i 1)

theorem stable_algebraMap (a : ℤ_[p]) : c.Stable (algebraMap _ _ a) (algebraMap _ _ a) :=
  (c.stable_iff _ _).2 fun x => by
    rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, Matrix.smul_mulVec, Matrix.one_mulVec,
      map_smul c.toTate]
    exact LinearMap.congr_fun (map_smul (tateMap G G O) a (𝟙 G)) _

theorem Stable.add {c : ConstTate ε G} {f g : End G} {ρ σ : Matrix (Fin G.height) (Fin G.height) ℤ_[p]}
    (hf : c.Stable f ρ) (hg : c.Stable g σ) : c.Stable (f + g) (ρ + σ) :=
  (c.stable_iff _ _).2 fun x => by
    rw [Matrix.add_mulVec, map_add c.toTate, ← (c.stable_iff _ _).1 hf, ← (c.stable_iff _ _).1 hg]
    exact LinearMap.congr_fun (map_add (tateEnd G O) f g) _

theorem Stable.mul {c : ConstTate ε G} {f g : End G} {ρ σ : Matrix (Fin G.height) (Fin G.height) ℤ_[p]}
    (hf : c.Stable f ρ) (hg : c.Stable g σ) : c.Stable (f * g) (ρ * σ) :=
  (c.stable_iff _ _).2 fun x => by
    rw [← Matrix.mulVec_mulVec, ← (c.stable_iff _ _).1 hf, ← (c.stable_iff _ _).1 hg]
    rfl

def al : (Fin G.height → O) →ₗ[O] G.dual.omega := Fintype.linearCombination O fun i => hodgeTate G (c.t i)

def alDual : G.Lie →ₗ[O] (Fin G.height → O) := LinearMap.pi fun j => Module.Dual.eval O _ (dlog G (c.t' j))

def W : Submodule O (Fin G.height → O) := LinearMap.ker c.al

theorem al_apply (x : Fin G.height → O) : c.al x = ∑ i, x i • hodgeTate G (c.t i) :=
  Fintype.linearCombination_apply ..

@[simp] theorem alDual_apply (x : G.Lie) (j : Fin G.height) : c.alDual x j = x (dlog G (c.t' j)) := rfl

theorem mem_W (x : Fin G.height → O) : x ∈ c.W ↔ c.al x = 0 := Iff.rfl

theorem omegaMap_dual_al (y : Fin G.height → O) :
    omegaMap _ _ G.bidual.hom (c.dual.al y) = ∑ j, y j • dlog G (c.t' j) := by
  rw [al_apply, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_smul, hodgeTate_apply, ← dlog_tateMap, ← tateMap_comp, ← dualHom_bidual_inv, ← dualHom_comp, Iso.hom_inv_id,
    dualHom_id, tateMap_id]
  rfl

theorem Stable.al {c : ConstTate ε G} {f : End G} {ρ : Matrix (Fin G.height) (Fin G.height) ℤ_[p]} (hf : c.Stable f ρ)
    (φ : ℤ_[p] →+* O) (x : Fin G.height → O) : c.al ((ρ.map φ).mulVec x) = omegaDualMap G G f (c.al x) := by
  simp only [al_apply, map_sum, map_smul, ← hodgeTate_tateMap, hf _, hodgeTate_smul φ, Finset.smul_sum, smul_smul,
    Matrix.mulVec, dotProduct, Finset.sum_smul, Matrix.map_apply]
  rw [Finset.sum_comm]
  simp only [mul_comm]

def ofConst (ε : (PDivGroup.mu p O).Tate) : ConstTate ε (const p O) where
  t _ := constGen p O
  t' _ := (charHom (const p O)).symm (constHom _ ε)
  pair i j := by
    rw [pairing_apply, LinearEquiv.apply_symm_apply, tateMap_constHom, if_pos (Subsingleton.elim (α := Fin 1) i j)]

def ofMu (ε : (PDivGroup.mu p O).Tate) : ConstTate ε (PDivGroup.mu p O) where
  t _ := ε
  t' _ := constGen p O
  pair i j := by
    rw [pairing_apply, charHom_constGen, tateMap_id, if_pos (Subsingleton.elim (α := Fin 1) i j)]

theorem exists_bijective (C : Type) [Field C] [Algebra O C] [IsIntegrallyClosedIn O C] [IsAlgClosed C] [CharZero C]
    (ε : (PDivGroup.mu p O).Tate) (G : PDivGroup p O) : ∃ c : ConstTate ε G, Function.Bijective c.toTate := by
  haveI := G.finite_tate C
  haveI := G.free_tate C
  let b := Module.finBasisOfFinrankEq ℤ_[p] G.Tate (G.finrank_tate C)
  choose χ hχ using fun j : Fin G.height => (G.pairing_flip_bijective C).2
    (LinearMap.toSpanSingleton ℤ_[p] _ ε ∘ₗ b.coord j)
  refine ⟨⟨b, χ, fun i j => (LinearMap.congr_fun (hχ j) (b i)).trans ?_⟩, ?_⟩
  · simp [Finsupp.single_apply]
  · have h : ∀ x, Fintype.linearCombination ℤ_[p] b x = b.equivFun.symm x := fun x => by
      simp [Fintype.linearCombination_apply]
    exact (funext h : ⇑(Fintype.linearCombination ℤ_[p] b) = _) ▸ b.equivFun.symm.bijective

section BaseChange

variable (O' : Type) [CommRing O'] [Algebra O O']

def baseChange {ε' : (PDivGroup.mu p O').Tate} (h : ∀ n, muRoot ε' n = algebraMap O O' (muRoot ε n)) :
    ConstTate ε' (G.baseChange O') where
  t i := bcTate O' (c.t i)
  t' j := bcChar O' (c.t' j)
  pair i j := muRoot_ext fun n => by
    rw [muRoot_pairing_bc, c.pair]
    split_ifs
    · exact (h n).symm
    · rw [muRoot_zero, muRoot_zero, map_one]

end BaseChange

end ConstTate

end Const

section Lattices

open scoped Pointwise

def piMap {A B : Type} [CommRing A] [CommRing B] (σ : A →+* B) (ι : Type) : (ι → A) →ₛₗ[σ] (ι → B) where
  toFun x i := σ (x i)
  map_add' x y := funext fun i => map_add σ (x i) (y i)
  map_smul' a x := funext fun i => map_mul σ a (x i)

@[simp] theorem piMap_apply {A B : Type} [CommRing A] [CommRing B] (σ : A →+* B) (ι : Type) (x : ι → A) (i : ι) :
    piMap σ ι x i = σ (x i) := rfl

section Quot

variable {R X : Type} [CommRing R] [AddCommGroup X] [Module R X]

def quotIncl (N : Submodule R X) {P Q : Submodule R X} (h : P ≤ Q) :
    (P ⧸ N.comap P.subtype) →ₗ[R] Q ⧸ N.comap Q.subtype :=
  Submodule.mapQ _ _ (Submodule.inclusion h) fun _ hx => hx

def quotProj {N P : Submodule R X} (h : N ≤ P) (Q : Submodule R X) :
    (Q ⧸ N.comap Q.subtype) →ₗ[R] Q ⧸ P.comap Q.subtype :=
  Submodule.mapQ _ _ LinearMap.id fun _ hx => h hx

theorem quot_exact {N P Q : Submodule R X} (h : N ≤ P) (h' : P ≤ Q) : Function.Injective (quotIncl N h') ∧
    Function.Exact (quotIncl N h') (quotProj h Q) ∧ Function.Surjective (quotProj h Q) := by
  refine ⟨(injective_iff_map_eq_zero _).2 fun x hx => ?_, fun x => ?_, fun x => ?_⟩
  · obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    have h1 : Submodule.inclusion h' x ∈ N.comap Q.subtype := (Submodule.Quotient.mk_eq_zero _).1 hx
    exact (Submodule.Quotient.mk_eq_zero _).2 h1
  · obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    refine ⟨fun hx => ?_, ?_⟩
    · have h1 : x ∈ P.comap Q.subtype := (Submodule.Quotient.mk_eq_zero _).1 hx
      exact ⟨Submodule.Quotient.mk ⟨x.1, h1⟩, rfl⟩
    · rintro ⟨y, hy⟩
      obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ y
      rw [← hy]
      exact (Submodule.Quotient.mk_eq_zero (P.comap Q.subtype) (x := Submodule.inclusion h' y)).2 y.2
  · obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    exact ⟨Submodule.Quotient.mk x, rfl⟩

end Quot

variable {p : ℕ} [Fact p.Prime]

section Ring

variable (S : CycPerfd p)

instance thetaSurjective : RingHomSurjective (fontaineTheta S.R p) := ⟨S.surj⟩

def eps : (PDivGroup.mu p S.R).Tate := muTate S.R (zeta S.ε) S.zeta_zero (zeta_succ_pow S.ε)

@[simp] theorem muRoot_eps (n : ℕ) : muRoot (eps S) n = zeta S.ε n := muRoot_muTate ..

theorem constHom_eps : constHom _ (eps S) = epsHom (zeta S.ε) S.zeta_zero (zeta_succ_pow S.ε) := rfl

def muN (n : ℕ) : Ainf p S.R := Sandwich.mu (root^[n] S.ε)

def xiN (n : ℕ) : Ainf p S.R := xi (root^[n] S.ε)

theorem xiN_mul_muN (n : ℕ) : xiN S n * muN S (n + 1) = muN S n := by
  rw [muN, Function.iterate_succ_apply']
  exact xi_mul_nu _

theorem phiInv_muN (n : ℕ) : phiInv p S.R (muN S n) = muN S (n + 1) := by
  rw [muN, muN, Function.iterate_succ_apply']
  exact phiInv_mu _

theorem phiInv_xiN (n : ℕ) : phiInv p S.R (xiN S n) = xiN S (n + 1) := by
  rw [xiN, xiN, Function.iterate_succ_apply', xi, xi, map_sum]
  simp only [map_pow, phiInv, WittVector.map_teichmuller]
  rfl

theorem frobenius_muN (n : ℕ) : frobenius (muN S (n + 1)) = muN S n := by
  rw [← phiInv_muN, Dieudonne.frobenius_phiInv]

theorem frobenius_xiN (n : ℕ) : frobenius (xiN S (n + 1)) = xiN S n := by
  rw [← phiInv_xiN, Dieudonne.frobenius_phiInv]

theorem theta_muN (n : ℕ) : fontaineTheta S.R p (muN S n) = zeta S.ε n - 1 := by
  rw [muN, Sandwich.mu, map_sub, fontaineTheta_teichmuller, map_one, zeta]

theorem zeta_one_sub_one_dvd : zeta S.ε 1 - 1 ∣ (p : S.R) := by
  have h : fontaineTheta S.R p (xi S.ε) = 0 := by
    rw [← RingHom.mem_ker, S.ker_eq]; exact mem_span_singleton_self _
  have h1 : ∑ i ∈ Finset.range p, zeta S.ε 1 ^ i = 0 := by
    simpa [xi, fontaineTheta_teichmuller, zeta] using h
  have h2 : (p : S.R) = -∑ i ∈ Finset.range p, (zeta S.ε 1 ^ i - 1) := by simp [h1]
  rw [h2, dvd_neg]
  exact Finset.dvd_sum fun i _ => sub_one_dvd_pow_sub_one _ i

theorem zeta_sub_one_dvd (n : ℕ) : zeta S.ε (n + 1) - 1 ∣ zeta S.ε 1 - 1 := by
  induction n with
  | zero => exact dvd_rfl
  | succ n ih => exact (zeta_succ_pow S.ε (n + 1) ▸ sub_one_dvd_pow_sub_one _ p).trans ih

theorem isSMulRegular_zeta_sub_one (n : ℕ) : IsSMulRegular S.R (zeta S.ε (n + 1) - 1) := by
  obtain ⟨a, ha⟩ := (zeta_sub_one_dvd S n).trans (zeta_one_sub_one_dvd S)
  exact IsSMulRegular.of_mul (a := a) (by rw [mul_comm, ← ha]; exact S.reg)

theorem zeta_one_ne_one : zeta S.ε 1 ≠ 1 := fun h => (Fact.out : ¬IsUnit (p : S.R)) <| by
  have h1 := isSMulRegular_zeta_sub_one S 0
  rw [zero_add, h, sub_self] at h1
  haveI := IsSMulRegular.zero_iff_subsingleton.1 h1
  exact isUnit_of_subsingleton _

theorem not_isUnit_zeta_sub_one : ¬IsUnit (zeta S.ε 1 - 1) := fun h => (Fact.out : ¬IsUnit (p : S.R)) <| by
  obtain ⟨r, hr⟩ := exists_add_pow_prime_eq (Fact.out : p.Prime) (zeta S.ε 1 - 1) 1
  rw [sub_add_cancel, zeta_succ_pow, S.zeta_zero, one_pow] at hr
  exact isUnit_of_dvd_unit ⟨-((zeta S.ε 1 - 1) * r), by linear_combination -hr⟩ (h.pow p)

theorem smul_eps_eq_zero (a : ℤ_[p]) (h : a • eps S = 0) : a = 0 := by
  by_contra ha
  rw [PadicInt.unitCoeff_spec ha, mul_smul, ← Units.smul_def, smul_eq_zero_iff_eq, ← Nat.cast_pow] at h
  have h1 := congrArg (muRoot · (a.valuation + 1)) h
  have h2 : ∀ k, zeta S.ε (k + 1) ^ p ^ k = zeta S.ε 1 := fun k => by
    induction k with
    | zero => simp
    | succ k ih => rw [pow_succ', pow_mul, zeta_succ_pow, ih]
  simp only [muRoot_smul, muRoot_zero] at h1
  rw [PDiv.pow_digit_natCast (muRoot_pow_self _ _), muRoot_eps, h2] at h1
  exact zeta_one_ne_one S h1

theorem muRoot_eps_of_over {S S' : CycPerfd p} [Algebra S.R S'.R] {α : Ainf p S.R →+* Ainf p S'.R} (h : S.Over S' α)
    (n : ℕ) : muRoot (eps S') n = algebraMap S.R S'.R (muRoot (eps S) n) := by
  have h1 : α (muN S n) = muN S' n := by
    induction n with
    | zero => exact (map_sub α (teichmuller p S.ε) 1).trans (by rw [h.2.2, map_one]; rfl)
    | succ n ih => exact Dieudonne.frobenius_injective (by rw [← h.2.1, frobenius_muN, frobenius_muN, ih])
  have h2 := h.1 (muN S n)
  rwa [h1, theta_muN, theta_muN, map_sub, map_one, sub_left_inj, ← muRoot_eps, ← muRoot_eps] at h2

def base (h : ℕ) : Submodule S.R (Fin h → S.R) := (zeta S.ε 1 - 1) • ⊤

theorem mem_base {h : ℕ} (x : Fin h → S.R) : x ∈ base S h ↔ ∃ y, (zeta S.ε 1 - 1) • y = x := by
  simp [base, Submodule.mem_smul_pointwise_iff_exists]

end Ring

variable (D : PrismData p) {S : CycPerfd p}

def PrismData.eCoord (S : CycPerfd p) : D.M S (const p S.R) ≃ₗ[Ainf p S.R] Ainf p S.R :=
  (LinearEquiv.ofBijective _ (D.e_bijective S)).symm

@[simp] theorem PrismData.eCoord_smul_e (a : Ainf p S.R) : D.eCoord S (a • D.e S) = a :=
  (LinearEquiv.ofBijective _ (D.e_bijective S)).symm_apply_apply a

@[simp] theorem PrismData.eCoord_smul (m : D.M S (const p S.R)) : D.eCoord S m • D.e S = m :=
  (LinearEquiv.ofBijective _ (D.e_bijective S)).apply_symm_apply m

theorem PrismData.eCoord_φ (m : D.M S (const p S.R)) : D.eCoord S (D.φ S _ m) = frobenius (D.eCoord S m) := by
  conv_lhs => rw [← D.eCoord_smul m, map_smulₛₗ, D.φ_e, D.eCoord_smul_e]

abbrev PrismData.Cov (G : PDivGroup p S.R) : Type := D.M S G.dual

def PrismData.covMap (G H : PDivGroup p S.R) : (G ⟶ H) →+ (D.Cov G →ₗ[Ainf p S.R] D.Cov H) :=
  (D.map S H.dual G.dual).comp (dualHom G H).toAddMonoidHom

def PrismData.toLie (G : PDivGroup p S.R) : D.Cov G →ₛₗ[fontaineTheta S.R p] G.Lie :=
  (lieMap _ G G.bidual.inv).comp (D.lie S G.dual)

def PrismData.Fil (G : PDivGroup p S.R) : Submodule (Ainf p S.R) (D.Cov G) := LinearMap.ker (D.toLie G)

theorem PrismData.toLie_surjective (G : PDivGroup p S.R) : Function.Surjective (D.toLie G) := fun x => by
  obtain ⟨m, hm⟩ := D.lie_surjective S G.dual (lieMap G _ G.bidual.hom x)
  refine ⟨m, (congrArg (lieMap _ G G.bidual.inv) hm).trans ?_⟩
  rw [← LinearMap.comp_apply, ← lieMap_comp, Iso.hom_inv_id, lieMap_id, LinearMap.id_apply]

theorem PrismData.mem_Fil (G : PDivGroup p S.R) (m : D.Cov G) :
    m ∈ D.Fil G ↔ ∃ n, D.φ S G.dual m = frobenius (xi S.ε) • n := by
  rw [← D.lie_eq_zero_iff]
  refine ⟨fun h => ?_, fun h => (congrArg (lieMap _ G G.bidual.inv) h).trans (map_zero _)⟩
  have h1 := LinearMap.congr_fun (lieMap_comp G.bidual.inv G.bidual.hom) (D.lie S G.dual m)
  have h2 : lieMap _ G G.bidual.inv (D.lie S G.dual m) = 0 := h
  rwa [Iso.inv_hom_id, lieMap_id, LinearMap.id_apply, LinearMap.comp_apply, h2, map_zero] at h1

variable {G : PDivGroup p S.R} (c : ConstTate (eps S) G)

def inj : (Fin G.height → Ainf p S.R) →ₗ[Ainf p S.R] D.Cov G :=
  Fintype.linearCombination (Ainf p S.R) fun i => D.map S G.dual (PDivGroup.mu p S.R) (dualChar G (c.t i)) (D.l S)

def coord : D.Cov G →ₗ[Ainf p S.R] (Fin G.height → Ainf p S.R) :=
  LinearMap.pi fun j => (D.eCoord S).toLinearMap ∘ₗ D.map S (const p S.R) G.dual (constHom G.dual (c.t' j))

theorem inj_apply (x : Fin G.height → Ainf p S.R) :
    inj D c x = ∑ i, x i • D.map S G.dual (PDivGroup.mu p S.R) (dualChar G (c.t i)) (D.l S) :=
  Fintype.linearCombination_apply ..

theorem coord_apply (m : D.Cov G) (j : Fin G.height) :
    coord D c m j = D.eCoord S (D.map S (const p S.R) G.dual (constHom G.dual (c.t' j)) m) := rfl

theorem coord_smul_e (m : D.Cov G) (j : Fin G.height) :
    coord D c m j • D.e S = D.covMap G (PDivGroup.mu p S.R) (charHom G (c.t' j)) m := by
  rw [coord_apply, D.eCoord_smul, ← dualHom_charHom]
  rfl

theorem coord_inj (x : Fin G.height → Ainf p S.R) : coord D c (inj D c x) = Sandwich.mu S.ε • x := by
  funext j
  have h : ∀ i, coord D c (D.map S G.dual (PDivGroup.mu p S.R) (dualChar G (c.t i)) (D.l S)) j =
      if i = j then Sandwich.mu S.ε else 0 := fun i => by
    rw [coord_apply, ← LinearMap.comp_apply, ← D.map_comp, constHom_comp_dualChar, c.pair]
    split_ifs
    · rw [constHom_eps, D.map_eps, D.eCoord_smul_e]
    · simp
  simp [inj_apply, Finset.sum_apply, h, mul_comm]

theorem coord_φ (m : D.Cov G) : coord D c (D.φ S G.dual m) = piMap frobenius _ (coord D c m) :=
  funext fun j => by rw [coord_apply, D.map_φ, D.eCoord_φ, piMap_apply, coord_apply]

def K (n : ℕ) : Submodule (Ainf p S.R) (Fin G.height → Ainf p S.R) :=
  Nat.rec (LinearMap.range (coord D c)) (fun _ N => N.comap (piMap frobenius _)) n

theorem K_zero : K D c 0 = LinearMap.range (coord D c) := rfl

theorem K_succ (n : ℕ) : K D c (n + 1) = (K D c n).comap (piMap frobenius _) := rfl

theorem mem_K_zero (x : Fin G.height → Ainf p S.R) : x ∈ K D c 0 ↔ ∃ m, coord D c m = x := Iff.rfl

theorem mem_K_succ (n : ℕ) (x : Fin G.height → Ainf p S.R) :
    x ∈ K D c (n + 1) ↔ piMap frobenius _ x ∈ K D c n := Iff.rfl

theorem mem_K (n : ℕ) (x : Fin G.height → Ainf p S.R) :
    x ∈ K D c n ↔ ∃ m, ∀ j, (phiInv p S.R)^[n] (coord D c m j) = x j := by
  induction n generalizing x with
  | zero => exact ⟨fun ⟨m, h⟩ => ⟨m, congrFun h⟩, fun ⟨m, h⟩ => ⟨m, funext h⟩⟩
  | succ n ih =>
    rw [mem_K_succ, ih]
    refine exists_congr fun m => forall_congr' fun j => ?_
    rw [Function.iterate_succ_apply', piMap_apply]
    exact ⟨fun h => by rw [h, Dieudonne.phiInv_frobenius], fun h => by rw [← h, Dieudonne.frobenius_phiInv]⟩

theorem muN_smul_mem_K (n : ℕ) (x : Fin G.height → Ainf p S.R) : muN S n • x ∈ K D c n := by
  induction n generalizing x with
  | zero => exact ⟨_, coord_inj D c x⟩
  | succ n ih => rw [mem_K_succ, map_smulₛₗ, frobenius_muN]; exact ih _

theorem xiN_smul_mem_K (n : ℕ) {x : Fin G.height → Ainf p S.R} (hx : x ∈ K D c (n + 1)) : xiN S n • x ∈ K D c n := by
  induction n generalizing x with
  | zero =>
    obtain ⟨m, hm⟩ := hx
    obtain ⟨k, hk⟩ := D.exists_φ_eq S G.dual m
    refine ⟨k, funext fun j => Dieudonne.frobenius_injective ?_⟩
    have h := congrFun (coord_φ D c k) j
    rw [hk, map_smul, hm] at h
    exact h.symm.trans (map_mul (frobenius : Ainf p S.R →+* Ainf p S.R) _ _).symm
  | succ n ih => rw [mem_K_succ, map_smulₛₗ, frobenius_xiN]; exact ih hx

theorem K_le_succ (n : ℕ) : K D c n ≤ K D c (n + 1) := by
  induction n with
  | zero => rintro _ ⟨m, rfl⟩; exact ⟨_, coord_φ D c m⟩
  | succ n ih => exact Submodule.comap_mono ih

def b : D.Cov G →ₛₗ[fontaineTheta S.R p] (Fin G.height → S.R) := (piMap (fontaineTheta S.R p) _).comp (coord D c)

theorem b_apply (m : D.Cov G) (j : Fin G.height) : b D c m j = fontaineTheta S.R p (coord D c m j) := rfl

def thetaK (n : ℕ) : Submodule S.R (Fin G.height → S.R) := (K D c n).map (piMap (fontaineTheta S.R p) _)

theorem thetaK_zero : thetaK D c 0 = LinearMap.range (b D c) := (LinearMap.range_comp _ _).symm

def H (n : ℕ) : Submodule S.R (Fin G.height → S.R) :=
  ((zeta S.ε 1 - 1) • thetaK D c (n + 1)).comap (LinearMap.lsmul S.R _ (zeta S.ε (n + 1) - 1))

theorem mem_H (n : ℕ) (x : Fin G.height → S.R) : x ∈ H D c n ↔ ∃ k ∈ K D c (n + 1),
    (zeta S.ε 1 - 1) • piMap (fontaineTheta S.R p) _ k = (zeta S.ε (n + 1) - 1) • x := by
  rw [H, Submodule.mem_comap, Submodule.mem_smul_pointwise_iff_exists]
  exact ⟨fun ⟨_, ⟨k, hk, rfl⟩, h⟩ => ⟨k, hk, h⟩, fun ⟨k, hk, h⟩ => ⟨_, ⟨k, hk, rfl⟩, h⟩⟩

theorem H_zero : H D c 0 = thetaK D c 1 := by
  ext x
  rw [mem_H]
  exact exists_congr fun k => and_congr_right fun _ =>
    ⟨fun h => funext fun j => isSMulRegular_zeta_sub_one S 0 (congrFun h j), fun h => by rw [h]⟩

theorem base_le_H (n : ℕ) : base S G.height ≤ H D c n := fun x hx => by
  obtain ⟨y, rfl⟩ := (mem_base S x).1 hx
  choose k hk using fun j => S.surj (y j)
  refine (mem_H D c n _).2 ⟨_, muN_smul_mem_K D c (n + 1) k, ?_⟩
  rw [map_smulₛₗ, theta_muN, smul_comm, show piMap (fontaineTheta S.R p) _ k = y from funext hk]

theorem H_succ_le (n : ℕ) : H D c (n + 1) ≤ H D c n := fun x hx => by
  obtain ⟨k, hk, h⟩ := (mem_H D c _ x).1 hx
  refine (mem_H D c n x).2 ⟨_, xiN_smul_mem_K D c (n + 1) hk, ?_⟩
  rw [map_smulₛₗ, smul_comm, h, smul_smul, ← theta_muN, ← map_mul, xiN_mul_muN, theta_muN]

abbrev LL (n : ℕ) : Type := H D c n ⧸ (H D c (n + 1)).comap (H D c n).subtype

abbrev QQ (r : ℕ) : Type := H D c r ⧸ (base S G.height).comap (H D c r).subtype

def qqIncl (r : ℕ) : QQ D c (r + 1) →ₗ[S.R] QQ D c r := quotIncl _ (H_succ_le D c r)

def qqProj (r : ℕ) : QQ D c r →ₗ[S.R] LL D c r := quotProj (base_le_H D c (r + 1)) _

theorem qq_exact (r : ℕ) : Function.Injective (qqIncl D c r) ∧ Function.Exact (qqIncl D c r) (qqProj D c r) ∧
    Function.Surjective (qqProj D c r) := quot_exact (base_le_H D c (r + 1)) (H_succ_le D c r)

theorem inj_const_surjective : Function.Surjective (inj D (ConstTate.ofConst (eps S))) := fun m => by
  obtain ⟨a, ha⟩ := (D.l_bijective S).2 (D.map S _ _ (PDivGroup.mu p S.R).bidual.hom m)
  have h : dualChar (const p S.R) (constGen p S.R) = (PDivGroup.mu p S.R).bidual.inv := by
    rw [← dualHom_constHom, show constHom _ (constGen p S.R) = 𝟙 _ by
      rw [← LinearEquiv.eq_symm_apply, constHom_symm_apply, tateMap_id], dualHom_id, Category.id_comp]
  refine ⟨fun _ => a, (inj_apply ..).trans ((Fin.sum_univ_one _).trans ?_)⟩
  change a • D.map S _ _ (dualChar (const p S.R) (constGen p S.R)) (D.l S) = m
  rw [h, ← map_smul, ← LinearMap.toSpanSingleton_apply, ha, ← LinearMap.comp_apply, ← D.map_comp, Iso.inv_hom_id,
    D.map_id, LinearMap.id_apply]

theorem H_eq_base (h : Function.Surjective (inj D c)) (n : ℕ) : H D c n = base S G.height := by
  have hK : ∀ n x, x ∈ K D c n → ∃ y, x = muN S n • y := fun n => by
    induction n with
    | zero => rintro _ ⟨m, rfl⟩; obtain ⟨y, rfl⟩ := h m; exact ⟨y, coord_inj D c y⟩
    | succ n ih =>
      intro x hx
      obtain ⟨y, hy⟩ := ih _ hx
      refine ⟨piMap (phiInv p S.R) _ y, ?_⟩
      rw [← phiInv_muN, ← map_smulₛₗ, ← hy]
      exact funext fun j => (Dieudonne.phiInv_frobenius _).symm
  refine le_antisymm (fun x hx => ?_) (base_le_H D c n)
  obtain ⟨k, hk, hx⟩ := (mem_H D c n x).1 hx
  obtain ⟨y, rfl⟩ := hK _ _ hk
  rw [map_smulₛₗ, theta_muN, smul_comm] at hx
  exact (mem_base S x).2 ⟨_, funext fun j => isSMulRegular_zeta_sub_one S n (congrFun hx j)⟩

theorem H_const (n : ℕ) : H D (ConstTate.ofConst (eps S)) n = base S 1 := H_eq_base D _ (inj_const_surjective D) n

theorem K_mu (n : ℕ) : K D (ConstTate.ofMu (eps S)) n = ⊤ := by
  induction n with
  | zero =>
    refine eq_top_iff.2 fun x _ => ⟨x (0 : Fin 1) • D.e S, funext fun j => ?_⟩
    change D.eCoord S (D.map S _ _ (constHom (const p S.R) (constGen p S.R)) _) = _
    rw [show constHom _ (constGen p S.R) = 𝟙 _ by rw [← LinearEquiv.eq_symm_apply, constHom_symm_apply, tateMap_id],
      D.map_id, LinearMap.id_apply, D.eCoord_smul_e, Subsingleton.elim (α := Fin 1) j 0]
  | succ n ih => rw [K_succ, ih, Submodule.comap_top]

theorem mem_H_mu (n : ℕ) (x : Fin 1 → S.R) :
    x ∈ H D (ConstTate.ofMu (eps S)) n ↔ (zeta S.ε (n + 1) - 1) • x ∈ base S 1 := by
  rw [mem_base]
  refine (mem_H D (ConstTate.ofMu (eps S)) n x).trans ⟨fun ⟨_, _, h⟩ => ⟨_, h⟩, fun ⟨y, h⟩ => ?_⟩
  choose k hk using fun j => S.surj (y j)
  exact ⟨k, by rw [K_mu]; trivial, (congrArg _ (funext hk)).trans h⟩

theorem H_mu_zero : H D (ConstTate.ofMu (eps S)) 0 = ⊤ ∧ base S 1 ≠ ⊤ := by
  refine ⟨eq_top_iff.2 fun x _ => (mem_H_mu D 0 x).2 ((mem_base S _).2 ⟨x, rfl⟩), fun h => ?_⟩
  obtain ⟨y, hy⟩ := (mem_base S (1 : Fin 1 → S.R)).1 (h ▸ Submodule.mem_top)
  exact not_isUnit_zeta_sub_one S (IsUnit.of_mul_eq_one _ (congrFun hy 0))

open scoped Formalism.Per in

theorem exists_constTate (p : ℕ) [Fact p.Prime] : ∃ S : CycPerfd p, IsPrimitiveRoot (zeta S.ε 1) p ∧
    ∀ G : PDivGroup p S.R, ∃ c : ConstTate (eps S) G, Function.Bijective c.toTate := by
  obtain ⟨e, he⟩ := GlobalTheory.MemLoc.Model.exists_isEps p
  have hv := PadicComplexInt.integers p
  haveI : IsIntegrallyClosedIn (Formalism.Per.OC p) ℂ_[p] := isIntegrallyClosedIn_iff.2
    ⟨hv.hom_inj, fun hx => hv.exists_of_le_one (hv.isIntegral_iff_v_le_one.1 hx)⟩
  have h := ConstTate.exists_bijective (p := p) (O := Formalism.Per.OC p) ℂ_[p]
  exact ⟨CycPerfd.ofIntegers p (Formalism.Per.OC p) hv e he.isPrimitiveRoot_untilt, he.isPrimitiveRoot_untilt, h _⟩

example : ∃ S : CycPerfd p, Nonempty (ConstTate (eps S) (Test.prod (PDivGroup.mu p S.R) (const p S.R))) :=
  (exists_constTate p).imp fun _ h => ⟨(h.2 _).choose⟩

example : (ConstTate.ofMu (eps S)).W = ⊤ ∧ (ConstTate.ofMu (eps S)).alDual (muLieGen p S.R) = 1 ∧
    thetaK D (ConstTate.ofMu (eps S)) 0 = ⊤ :=
  ⟨eq_top_iff.2 fun _ _ => Subsingleton.elim (α := (const p S.R).omega) _ _,
    funext fun _ => (congrArg (muLieGen p S.R) (dlog_constGen (p := p) (O := S.R))).trans (muLieGen_dlogT p S.R),
    eq_top_iff.2 fun y _ => by
      choose k hk using fun j => S.surj (y j)
      exact ⟨k, by rw [K_mu]; trivial, funext hk⟩⟩

example : (ConstTate.ofConst (eps S)).al 1 ≠ 0 := fun h => by
  have h1 := ((ConstTate.ofConst (eps S)).al_apply 1).trans (Fin.sum_univ_one _)
  exact (Test.hodgeTate_values (Fact.out : ¬IsUnit (p : S.R))).2 ((one_smul S.R _).symm.trans (h1.symm.trans h))

example {S' : CycPerfd p} [Algebra S.R S'.R] {α : Ainf p S.R →+* Ainf p S'.R} (h : S.Over S' α) :
    ConstTate (eps S') (G.baseChange S'.R) := c.baseChange S'.R (muRoot_eps_of_over h)

end Lattices

end GlobalTheory.PerfdLat

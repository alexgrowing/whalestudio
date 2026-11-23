import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.GrNormCompCast
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLengthOneChainIdentityEmbedding
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDvrPowEqPrime

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

open CategoryTheory Limits AlgebraicGeometry IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.DV Formalism.L2.Pj Formalism.L2.Geo
open GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Vert GlobalTheory.LocM GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Mean4O GlobalTheory.MixedLocalChains GlobalTheory.BundleChernComparison

namespace GlobalTheory.ChainPts

def LocFreeMod {X : Scheme.{0}} (g : Γ(X, ⊤)) (F : X.Modules) : Prop :=
  ∀ x : X, ∃ (U : X.Opens) (r : ℕ), x ∈ U ∧ Nonempty ((Scheme.Modules.pullback U.ι).obj F ≅
    (Scheme.Modules.pullback U.ι).obj (cokernel (smulHom (freeModule X (Fin r)) g)))

example {X : Scheme.{0}} (g : Γ(X, ⊤)) (r : ℕ) : LocFreeMod g (cokernel (smulHom (freeModule X (Fin r)) g)) :=
  fun _ => ⟨⊤, r, trivial, ⟨Iso.refl _⟩⟩

section Eq

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (p : ℕ) [Fact p.Prime] [CharZero O]
  [CharP (ResidueField O) p] (B : Vert.Model O) (Λ : Type) [CommRing Λ]

abbrev AM : Type 1 := Action B.X.Modules Λ

variable {B Λ}

def IsAdd (M : AM B Λ) : Prop := ∀ a b : Λ, (M.ρ (a + b) : M.V ⟶ M.V) = (M.ρ a : M.V ⟶ M.V) + (M.ρ b : M.V ⟶ M.V)

def smulA (M : AM B Λ) (g : Γ(B.X, ⊤)) : M ⟶ M := ⟨smulHom M.V g, fun _ => by first | exact (smulHom_comp _ _).symm | exact smulHom_comp _ _⟩

def frobFun (h : (p : Γ((fibI p B).subscheme, ⊤)) = 0) : B.X.Modules ⥤ B.X.Modules :=
  Scheme.Modules.pullback (GlobalTheory.SS.FrobField.absFrob _ p 1 Fact.out h ≫ (fibI p B).subschemeι) ⋙
    Scheme.Modules.pushforward (fibI p B).subschemeι

def frobA (h : (p : Γ((fibI p B).subscheme, ⊤)) = 0) (M : AM B Λ) : AM B Λ := ((frobFun p h).mapAction Λ).obj M

theorem isFrob_frobA (h : (p : Γ((fibI p B).subscheme, ⊤)) = 0) (M : AM B Λ) : IsFrob p M.V (frobA p h M).V :=
  ⟨h, ⟨Iso.refl _⟩⟩

variable (B Λ) in

structure EPres where
  r : ℕ
  E : AM B Λ
  E' : AM B Λ
  add : IsAdd E
  add' : IsAdd E'
  vb : GlobalTheory.VB.IsVB E.V r
  vb' : GlobalTheory.VB.IsVB E'.V r
  ψ : E' ⟶ E
  iso : IsIso (B.genRes.map ψ.hom)

def EPres.toPres (P : EPres B Λ) : Pres B := ⟨P.r, P.E.V, P.E'.V, P.vb, P.vb', P.ψ.hom, P.iso⟩

def EPres.mod (P : EPres B Λ) : AM B Λ := cokernel P.ψ

def IsExtA (F₁ F₂ F₃ : AM B Λ) : Prop := ∃ S : ShortComplex (AM B Λ), S.ShortExact ∧
  Nonempty (S.X₁ ≅ F₁) ∧ Nonempty (S.X₂ ≅ F₂) ∧ Nonempty (S.X₃ ≅ F₃)

variable (B Λ) in

structure EqChain (o : ℕ) where
  π : Γ(B.X, ⊤)
  g : Γ(B.X, ⊤)
  γ : ℕ → Γ(B.X, ⊤)
  π_root : IsRootOfP p π (p - 1)
  g_root : IsRootOfP p g p
  γ_root : ∀ n < o, IsRootOfP p (γ n) (p ^ (n + 1))
  hp : (p : Γ((fibI p B).subscheme, ⊤)) = 0
  lw : EPres B Λ
  wl : lw.E ⟶ lw.E'
  lw_wl : lw.ψ ≫ wl = smulA _ π
  oo : EPres B Λ
  q : ℕ → EPres B Λ
  l : ℕ → EPres B Λ
  c3 : IsExtA (cokernel wl) (q 0).mod oo.mod
  step : ∀ n < o, IsExtA (q (n + 1)).mod (q n).mod (l n).mod
  l_free : ∀ n < o, LocFreeMod (γ n) (l n).mod.V
  l_last : ∀ n < o, Nonempty ((frobA p hp)^[n + 1] (l n).mod ≅ cokernel (smulA lw.E' (p : Γ(B.X, ⊤))))
  q_kill : ∀ n < o, Kills g (q (n + 1)).mod.V
  q_frob : ∀ n < o, Nonempty ((q n).mod ≅ frobA p hp (q (n + 1)).mod)

end Eq

namespace Examples₂

open GlobalTheory.MixedLocalChains.ChainOne

section Gen

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {B : Vert.Model O} {Λ : Type} [CommRing Λ]
  (χ : Λ →+* ℤ)

def Sc (M : AM B Λ) : Prop := ∀ c, (M.ρ c : M.V ⟶ M.V) = χ c • 𝟙 M.V

def mkA (F : B.X.Modules) : AM B Λ := ⟨F, ((Int.castRingHom (End F)).comp χ).toMonoidHom⟩

theorem sc_mkA (F : B.X.Modules) : Sc χ (mkA χ F) := fun c => by
  change ((χ c : ℤ) : End F) = χ c • (1 : End F)
  simp

variable {χ}

theorem Sc.isAdd {M : AM B Λ} (h : Sc χ M) : IsAdd M := fun a b => by
  rw [h, h, h, map_add, add_smul]

def liftIso {M N : AM B Λ} (hM : Sc χ M) (hN : Sc χ N) (e : M.V ≅ N.V) : M ≅ N :=
  Action.mkIso e fun c => by
    change (M.ρ c : M.V ⟶ M.V) ≫ e.hom = e.hom ≫ (N.ρ c : N.V ⟶ N.V)
    rw [hM, hN]; simp

def cokV {M N : AM B Λ} (f : M ⟶ N) : (cokernel f).V ≅ cokernel f.hom :=
  PreservesCokernel.iso (Action.forget B.X.Modules Λ) f

theorem Sc.coker {M N : AM B Λ} (f : M ⟶ N) (hN : Sc χ N) : Sc χ (cokernel f) := fun c => by
  have : Epi (cokernel.π f).hom := inferInstanceAs (Epi ((Action.forget B.X.Modules Λ).map (cokernel.π f)))
  have h : (N.ρ c : N.V ⟶ N.V) ≫ (cokernel.π f).hom = (cokernel.π f).hom ≫ ((cokernel f).ρ c : (cokernel f).V ⟶ _) :=
    (cokernel.π f).comm c
  rw [← cancel_epi (cokernel.π f).hom, ← h, hN]; simp

variable (p : ℕ) [Fact p.Prime]

theorem additive_frobFun (h : (p : Γ((fibI p B).subscheme, ⊤)) = 0) : (frobFun p h).Additive := by
  unfold frobFun
  infer_instance

theorem Sc.frob (h : (p : Γ((fibI p B).subscheme, ⊤)) = 0) {M : AM B Λ} (hM : Sc χ M) : Sc χ (frobA p h M) := fun c => by
  haveI := additive_frobFun p h
  change (frobFun p h).map (M.ρ c : M.V ⟶ M.V) = χ c • 𝟙 ((frobFun p h).obj M.V)
  rw [hM, Functor.map_zsmul, CategoryTheory.Functor.map_id]

theorem frob_act (h : (p : Γ((fibI p B).subscheme, ⊤)) = 0) {M : AM B Λ} (c : Λ) (g : Γ(B.X, ⊤))
    (hM : (M.ρ c : M.V ⟶ M.V) = smulHom M.V g) :
    ((frobA p h M).ρ c : (frobA p h M).V ⟶ (frobA p h M).V) = smulHom _ (g ^ p) := by
  change (frobFun p h).map (M.ρ c : M.V ⟶ M.V) = _
  rw [hM]
  unfold frobFun
  rw [Functor.comp_map, VB.pullback_map_smulHom, GlobalTheory.MixedLocalChains.FrobQuot.appTop_absFrob_comp p B h g, ← map_pow]
  exact pushforward_map_smulHom _ _ _

end Gen

section Base

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {Λ : Type} [CommRing Λ] (χ : Λ →+* ℤ)

abbrev sA (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] : AM (Model.base O) Λ := mkA χ (sO O)

def eMul {a : O} (ha : a ≠ 0) : EPres (Model.base O) Λ where
  r := 1
  E := sA χ O
  E' := sA χ O
  add := (sc_mkA χ _).isAdd
  add' := (sc_mkA χ _).isAdd
  vb := VB.isVB_structureModule _
  vb' := VB.isVB_structureModule _
  ψ := smulA (sA χ O) (cst O a)
  iso := Model.isIso_genRes_map_smulHom (Z := Model.base O) (sO O) ha

theorem smulA_mul (a b : O) : smulA (sA χ O) (cst O a) ≫ smulA (sA χ O) (cst O b) = smulA (sA χ O) (cst O (b * a)) := by
  apply Action.Hom.ext
  change smulHom (sO O) _ ≫ smulHom (sO O) _ = smulHom (sO O) _
  rw [← smulHom_mul, ← map_mul]

theorem isExtA_mul {a b c : O} (hb : b ≠ 0) (h : b * a = c) :
    IsExtA (cokernel (smulA (sA χ O) (cst O a))) (cokernel (smulA (sA χ O) (cst O c))) (cokernel (smulA (sA χ O) (cst O b))) := by
  haveI : Mono (smulA (sA χ O) (cst O b)) :=
    (Action.forget _ Λ).mono_of_mono_map (mono_smulHom_const hb)
  exact ⟨_, shortExact_cokernel_comp (smulA (sA χ O) (cst O a)) (smulA (sA χ O) (cst O b)),
    ⟨Iso.refl _⟩, ⟨cokernelIsoOfEq (by rw [smulA_mul, h])⟩, ⟨Iso.refl _⟩⟩

def freeOne (X : Scheme.{0}) : freeModule X (Fin 1) ≅ structureModule X :=
  coproductUniqueIso (fun _ : Fin 1 => structureModule X)

variable (p : ℕ) [Fact p.Prime] [CharZero O] [CharP (ResidueField O) p]

theorem frob_cok (h : (p : Γ((fibI p (Model.base O)).subscheme, ⊤)) = 0) {M : AM (Model.base O) Λ} (a : O)
    (ha : a ^ p ∣ (p : O)) (e : M.V ≅ cokernel (smulHom (sO O) (cst O a))) :
    Nonempty ((frobA p h M).V ≅ cokernel (smulHom (sO O) (cst O (a ^ p)))) := by
  obtain ⟨h', ⟨e'⟩⟩ := GlobalTheory.MixedLocalChains.isFrob_cokernel_smulHom_pow O p (Model.base O) (cst O a)
    (by rw [← map_pow, ← map_natCast (cst O) p]; exact map_dvd _ ha)
  rw [map_pow]
  exact ⟨(frobFun p h).mapIso e ≪≫ e'.symm⟩

theorem frob_iter (h : (p : Γ((fibI p (Model.base O)).subscheme, ⊤)) = 0) {M : AM (Model.base O) Λ} (hM : Sc χ M) (a : O)
    (e : M.V ≅ cokernel (smulHom (sO O) (cst O a))) (i : ℕ) (ha : a ^ p ^ i ∣ (p : O)) :
    Sc χ ((frobA p h)^[i] M) ∧ Nonempty (((frobA p h)^[i] M).V ≅ cokernel (smulHom (sO O) (cst O (a ^ p ^ i)))) := by
  induction i with
  | zero => exact ⟨hM, ⟨by rw [pow_zero, pow_one]; exact e⟩⟩
  | succ i ih =>
    have hp : 0 < p := (Fact.out : p.Prime).pos
    obtain ⟨h1, ⟨e1⟩⟩ := ih ((pow_dvd_pow a (Nat.pow_le_pow_right hp (Nat.le_succ i))).trans ha)
    rw [Function.iterate_succ_apply']
    rw [pow_succ, pow_mul] at ha ⊢
    exact ⟨h1.frob p h, frob_cok p h _ ha e1⟩

theorem exists_eqChain (o : ℕ) (ϖ : O) (u : Oˣ) (hu : ϖ ^ (p ^ (o + 1) * (p - 1)) = u * p) :
    ∃ Q : EqChain p (Model.base O) Λ o, Q.lw.r = 1 ∧ Sc χ Q.lw.E' ∧ (∀ n, ¬ IsZero (Q.q n).mod.V) ∧
      ∀ n, ¬ IsZero (Q.l n).mod.V := by
  have hp2 : 2 ≤ p := (Fact.out : p.Prime).two_le
  have hpos : ∀ k, 0 < p ^ k * (p - 1) := fun k => Nat.mul_pos (pow_pos (by omega) _) (by omega)
  have h0 : ϖ ≠ 0 := by
    rintro rfl
    rw [zero_pow (hpos _).ne', eq_comm] at hu
    exact GlobalTheory.Vert.natCast_ne_zero O p ((Units.mul_right_eq_zero u).1 hu)
  have hnu : ¬ IsUnit ϖ := fun h => by
    have : IsUnit ((u : O) * p) := by rw [← hu]; exact h.pow _
    exact (mem_maximalIdeal _).1 (GlobalTheory.Vert.natCast_mem_maximalIdeal O p)
      (isUnit_of_mul_isUnit_right this)
  have hn : ∀ k, ϖ ^ k ≠ 0 := fun k => pow_ne_zero _ h0
  have root : ∀ k a, k * a = p ^ (o + 1) * (p - 1) → IsRootOfP p (B := Model.base O) (cst O (ϖ ^ k)) a := fun k a h =>
    ⟨Units.map (cst O).toMonoidHom u, by
      rw [Units.coe_map, ← map_pow, ← pow_mul, h, hu, map_mul, map_natCast] <;> rfl⟩
  have dvdp : ∀ k, k ≤ p ^ (o + 1) * (p - 1) → ϖ ^ k ∣ (p : O) := fun k hk => (pow_dvd_pow ϖ hk).trans
    ⟨↑u⁻¹, by rw [hu, mul_comm (u : O), mul_assoc, Units.mul_inv, mul_one]⟩
  have hp := GlobalTheory.MixedLocalChains.FrobQuot.natCast_eq_zero_fibI p (Model.base O)
  have sc : ∀ a : Γ((Model.base O).X, ⊤), Sc χ (cokernel (smulA (sA χ O) a)) := fun a => Sc.coker _ (sc_mkA χ _)
  have ev : ∀ a : Γ((Model.base O).X, ⊤), (cokernel (smulA (sA χ O) a)).V ≅ cokernel (smulHom (sO O) a) :=
    fun a => cokV _
  have hγ : ∀ n < o, p ^ (o - n) * (p - 1) * p ^ (n + 1) = p ^ (o + 1) * (p - 1) := fun n h => by
    rw [mul_right_comm, ← pow_add]; congr 2; omega
  have hle : ∀ k ≤ o + 1, p ^ k ≤ p ^ (o + 1) * (p - 1) := fun k hk =>
    (Nat.pow_le_pow_right (by omega) hk).trans (Nat.le_mul_of_pos_right _ (by omega))
  haveI : IsIso (smulHom (sO O) ((cst O) ↑u)) :=
    (isUnit_iff_isIso _).1 ((u.isUnit.map (cst O)).map (smulEnd (sO O)))
  have eLast : cokernel (smulHom (sO O) ((cst O) (ϖ ^ (p ^ (o + 1) * (p - 1))))) ≅
      cokernel (smulHom (sO O) (p : Γ((Model.base O).X, ⊤))) :=
    cokernelIsoOfEq (by rw [hu, map_mul, map_natCast, smulHom_mul]) ≪≫
      cokernelCompIsIso (smulHom (sO O) (p : Γ((Model.base O).X, ⊤))) (smulHom (sO O) ((cst O) ↑u))
  refine ⟨{
      π := cst O (ϖ ^ p ^ (o + 1)), g := cst O (ϖ ^ (p ^ o * (p - 1))), γ := fun n => cst O (ϖ ^ (p ^ (o - n) * (p - 1))),
      π_root := root _ _ rfl,
      g_root := root _ _ (by ring),
      γ_root := fun n h => root _ _ (hγ n h),
      hp := hp,
      lw := eMul χ (one_ne_zero (α := O)), wl := smulA (sA χ O) (cst O (ϖ ^ p ^ (o + 1))),
      lw_wl := (smulA_mul χ _ _).trans (by rw [mul_one]; rfl),
      oo := eMul χ (one_ne_zero (α := O)),
      q := fun n => eMul χ (hn (p ^ (o + 1 - n))),
      l := fun n => eMul χ (hn (p ^ (o - n) * (p - 1))),
      c3 := isExtA_mul χ one_ne_zero (one_mul _),
      step := fun n h => isExtA_mul χ (hn _) ?_,
      l_free := fun n h x => ⟨⊤, 1, trivial, ⟨(Scheme.Modules.pullback _).mapIso (ev _ ≪≫
        cokernel.mapIso _ _ (freeOne _).symm (freeOne _).symm (smulHom_comp _ _))⟩⟩,
      l_last := fun n h => ?_,
      q_kill := fun n h => ?_,
      q_frob := fun n h => ?_ }, rfl, sc_mkA χ _, fun n h => ?_, fun n h => ?_⟩
  · rw [← pow_add]
    congr 1
    rw [show o + 1 - (n + 1) = o - n by omega, show o + 1 - n = o - n + 1 by omega, pow_succ]
    obtain ⟨q, rfl⟩ : ∃ q, p = q + 1 := ⟨p - 1, by omega⟩
    simp [mul_add]
  · obtain ⟨h1, ⟨e1⟩⟩ := frob_iter χ p hp (sc _) (ϖ ^ (p ^ (o - n) * (p - 1))) (ev _) (n + 1)
      (by rw [← pow_mul, hγ n h]; exact dvdp _ le_rfl)
    rw [← pow_mul, hγ n h] at e1
    exact ⟨liftIso h1 (sc _) (e1 ≪≫ eLast ≪≫ (ev _).symm)⟩
  · have k : Kills (cst O (ϖ ^ (p ^ o * (p - 1)))) (cokernel (smulHom (sO O) (cst O (ϖ ^ p ^ (o + 1 - (n + 1)))))) :=
      kills_cokernel (map_dvd _ (pow_dvd_pow _ ((Nat.pow_le_pow_right (by omega) (by omega)).trans
        (Nat.le_mul_of_pos_right (p ^ o) (by omega)))))
    have e := ev (cst O (ϖ ^ p ^ (o + 1 - (n + 1))))
    change smulHom (cokernel (smulA (sA χ O) (cst O (ϖ ^ p ^ (o + 1 - (n + 1)))))).V _ = 0
    rw [← cancel_mono e.hom, smulHom_comp, zero_comp]
    unfold Kills at k
    rw [k, comp_zero]
  · obtain ⟨e1⟩ := frob_cok p hp (ϖ ^ p ^ (o + 1 - (n + 1))) (by
      rw [← pow_mul, ← pow_succ]; exact dvdp _ (hle _ (by omega))) (ev _)
    rw [← pow_mul, ← pow_succ, show o + 1 - (n + 1) + 1 = o + 1 - n by omega] at e1
    exact ⟨liftIso (sc _) ((sc _).frob p hp) (ev _ ≪≫ e1.symm)⟩
  · exact not_isZero_cokernel (a := ϖ ^ p ^ (o + 1 - n))
      (by rw [isUnit_pow_iff (pow_pos (by omega) _).ne']; exact hnu) (h.of_iso (ev _).symm)
  · exact not_isZero_cokernel (a := ϖ ^ (p ^ (o - n) * (p - 1)))
      (by rw [isUnit_pow_iff (hpos _).ne']; exact hnu) (h.of_iso (ev _).symm)

end Base

theorem exists_base_eqChain (p : ℕ) [Fact p.Prime] (o : ℕ) (Λ : Type) [CommRing Λ] (χ : Λ →+* ℤ) :
    ∃ (O : Type) (_ : CommRing O) (_ : IsDomain O) (_ : IsDiscreteValuationRing O) (_ : CharZero O)
      (_ : CharP (ResidueField O) p) (Q : EqChain p (Model.base O) Λ o),
      Q.lw.r = 1 ∧ Sc χ Q.lw.E' ∧ (∀ n, ¬ IsZero (Q.q n).mod.V) ∧ ∀ n, ¬ IsZero (Q.l n).mod.V := by
  have hp2 : 2 ≤ p := (Fact.out : p.Prime).two_le
  obtain ⟨O, _, _, _, _, _, ϖ, h⟩ := GlobalTheory.RootDVR.exists_dvr_pow_eq_prime p (p ^ (o + 1) * (p - 1))
    (Nat.mul_pos (pow_pos (by omega) _) (by omega))
  exact ⟨O, _, _, _, inferInstance, inferInstance, exists_eqChain χ p o ϖ 1 (by simpa using h)⟩

theorem isExt_of_isExtA {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {B : Vert.Model O} {Λ : Type}
    [CommRing Λ] {P₁ P₂ P₃ : EPres B Λ} (h : IsExtA P₁.mod P₂.mod P₃.mod) :
    IsExt P₁.toPres.mod P₂.toPres.mod P₃.toPres.mod := by
  obtain ⟨S, hS, ⟨e₁⟩, ⟨e₂⟩, ⟨e₃⟩⟩ := h
  exact ⟨S.map (Action.forget _ Λ), hS.map_of_exact _, ⟨(Action.forget _ Λ).mapIso e₁ ≪≫ cokV _⟩,
    ⟨(Action.forget _ Λ).mapIso e₂ ≪≫ cokV _⟩, ⟨(Action.forget _ Λ).mapIso e₃ ≪≫ cokV _⟩⟩

end Examples₂

section Free

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {Xo : ∀ l : Level H, Moduli Dw l} {p : ℕ} {W : ValuationSubring ℂ} {Y : LocalSystem Xo p W} {i₀ : Idx H p}

def IsEqLatPres (Z : LocM.Mdl Y i₀) {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {B : Vert.Model O}
    (h : B.X ⟶ Z.X) {r : ℕ} (x : Fin r → Letter Dw) (d : Bool) (P : EPres B (𝓞 E)) : Prop :=
  P.r = r ∧ ∃ s : ∀ a : Fin Z.m, Fin r → Γ(P.E'.V, h ⁻¹ᵁ (Z.U a).1),
    IsLat Z h x d d P.E'.V s ∧ IsLat Z h x d (!d) P.E.V (fun a i => P.ψ.hom.app _ (s a i)) ∧
    ∀ (a : Fin Z.m) (i : Fin r) (c : 𝓞 E), (P.E'.ρ c : P.E'.V ⟶ P.E'.V).app _ (s a i) =
      (h.app (Z.U a).1).hom (Z.alg a (embK Z.i.c (x i).1 (if d then H.bar c else c))) • s a i

theorem IsEqLatPres.isLatPres {Z : LocM.Mdl Y i₀} {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    {B : Vert.Model O} {h : B.X ⟶ Z.X} {r : ℕ} {x : Fin r → Letter Dw} {d : Bool} {P : EPres B (𝓞 E)}
    (k : IsEqLatPres Z h x d P) : IsLatPres Z h x d P.toPres :=
  ⟨k.1, k.2.imp fun _ k' => ⟨k'.1, k'.2.1⟩⟩

end Free

def HasEqChain {D : D7} {A : Amb D} {N j : ℕ} {S : Sig A N j} {κ : Lv A} {p : ℕ} [Fact p.Prime] {hp : p.Prime}
    {W : ValuationSubring ℂ} {hW : (p : ℂ) ∈ W.nonunits} (z : AdmAt S κ hp hW) (o : ℕ) : Prop :=
  haveI := isDiscreteValuationRing_V z.Z.i.c hp hW
  haveI := charP_residueField_of_mem_nonunits z.Z.i.c hp hW
  ∀ c : (nmodel z.Z).Comp, ∃ (B : Vert.Model (z.Z.i.c.V W)) (f : Vert.Model.Hom B ((nmodel z.Z).comp c))
    (Q : EqChain p B (𝓞 D.host.E) o), GlobalTheory.IsNormalScheme B.X ∧ f.relDim = 0 ∧
      IsEqLatPres z.Z (f.f ≫ (nmodel z.Z).compι c) (xAll S) false Q.lw ∧
      IsEqLatPres z.Z (f.f ≫ (nmodel z.Z).compι c) (fun k => xAll S k.rev) true Q.oo

def EqChainSt : Prop := AtAll fun _ _ _ _ _ _ _ z => ∀ o, HasEqChain z o

end GlobalTheory.ChainPts

end

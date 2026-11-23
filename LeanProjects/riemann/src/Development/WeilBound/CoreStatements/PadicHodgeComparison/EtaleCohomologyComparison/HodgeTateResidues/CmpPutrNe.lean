import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.HodgeTateResidues.IsFirstChernClassInFamily
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.Imports
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CmpPutSucc

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory Polynomial

universe w w' v u v' u'

namespace CrystallineSemistableComparison.HT.Rees

open CH B GlobalTheory.CompanionTheory.ReesDown

section
variable {R : Type} [CommRing R] {D : Type u} [Category.{v} D] {F : D ⥤ ModuleCat.{w} R} (Ψ : Flt F)

def putr (r j : ℕ) (z : Cn (Ψ.S r).fn j) : Cn Ψ.rees j := fun s =>
  show Ψ.Pr _ from Pi.single (M := fun r => (Ψ.S r).S (s.obj (Fin.last j))) r (z s)

theorem cmp_putr (r j : ℕ) (z : Cn (Ψ.S r).fn j) : cmp Ψ r j (putr Ψ r j z) = (Ψ.S r).inc.pullC j z :=
  funext fun s => congrArg Subtype.val (Pi.single_eq_same (M := fun r => (Ψ.S r).S (s.obj (Fin.last j))) r (z s))

theorem cmp_putr_ne {r r' : ℕ} (h : r' ≠ r) (j : ℕ) (z : Cn (Ψ.S r).fn j) : cmp Ψ r' j (putr Ψ r j z) = 0 :=
  funext fun s => congrArg Subtype.val (Pi.single_eq_of_ne (M := fun r => (Ψ.S r).S (s.obj (Fin.last j))) h (z s))

theorem putr_d (r j : ℕ) (z : Cn (Ψ.S r).fn j) : d Ψ.rees j (putr Ψ r j z) = putr Ψ r (j + 1) (d _ j z) := by
  refine cochain_ext Ψ fun r' => ?_
  rw [cmp_d]
  by_cases h : r' = r
  · subst h
    rw [cmp_putr, cmp_putr, Mor.d_pullC]
  · rw [cmp_putr_ne Ψ h, cmp_putr_ne Ψ h, map_zero]

theorem putr_zero (r j : ℕ) : putr Ψ r j 0 = 0 := by
  refine cochain_ext Ψ fun r' => ?_
  by_cases h : r' = r
  · subst h
    rw [cmp_putr, map_zero]; rfl
  · rw [cmp_putr_ne Ψ h]; rfl

theorem putr_mem_B (r j : ℕ) (a : Cn (Ψ.S r).fn j) (h : a ∈ (cx (Ψ.S r).fn).B j) : putr Ψ r j a ∈ (cx Ψ.rees).B j := by
  cases j with
  | zero =>
    have : a = 0 := h
    rw [this, putr_zero]
    exact Submodule.zero_mem _
  | succ j =>
    obtain ⟨e, rfl⟩ := h
    exact ⟨putr Ψ r j e, putr_d Ψ r j e⟩

theorem inc_inj (r j : ℕ) {a b : Cn (Ψ.S r).fn j} (h : (Ψ.S r).inc.pullC j a = (Ψ.S r).inc.pullC j b) : a = b :=
  funext fun s => Subtype.ext (congrFun h s)

theorem inc_cmpS (r j : ℕ) (f : Cn Ψ.rees j) : (Ψ.S r).inc.pullC j (cmpS Ψ r j f) = cmp Ψ r j f := rfl

theorem cmpS_d (r j : ℕ) (f : Cn Ψ.rees j) : cmpS Ψ r (j + 1) (d Ψ.rees j f) = d _ j (cmpS Ψ r j f) :=
  inc_inj Ψ r _ (by rw [inc_cmpS, cmp_d, ← Mor.d_pullC, inc_cmpS])

theorem cmpS_mem_B (r j : ℕ) (a : Cn Ψ.rees j) (h : a ∈ (cx Ψ.rees).B j) : cmpS Ψ r j a ∈ (cx (Ψ.S r).fn).B j := by
  cases j with
  | zero =>
    have : a = 0 := h
    rw [this]
    exact Submodule.zero_mem _
  | succ j =>
    obtain ⟨e, rfl⟩ := h
    exact ⟨cmpS Ψ r j e, (cmpS_d Ψ r j e).symm⟩

theorem cmp_X_pow' (j r k : ℕ) (f : Cn Ψ.rees j) : cmp Ψ (r + k) j ((X : ℤ[X]) ^ k • f) = Ψ.μ ^ k • cmp Ψ r j f := by
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ', mul_smul, ← add_assoc, cmp_X, ih, pow_succ', mul_smul]

end

variable {R : Type} [CommRing R] {C : Type u} [Category.{v} C] {C' : Type u'} [Category.{v'} C'] {F : C ⥤ ModuleCat.{w} R}
  (Φ : Flt F) (G : C' ⥤ C) {n N : ℕ}

theorem inj (hRI : RI ((X : ℤ[X]) ^ N) n Φ.rees G) {j : ℕ} (hj : j ≤ n) (r : ℕ) (h) (x : H (Φ.S r).fn j)
    (hx : (Mor.restrict (Φ.S r).fn G).pull j x = 0) : (mulSub (Φ.μ ^ N) (Φ.S r) (Φ.S (r + N)) h).pull j x = 0 := by
  have hU : UpTo ((X : ℤ[X]) ^ N) ((Mor.restrict Φ.rees G).pull j) := hRI j hj
  obtain ⟨z, hz, rfl⟩ := (P.cls_surj (cx (Φ.S r).fn) j).1 x
  have hpd : d (G ⋙ (Φ.S r).fn) j ((Mor.restrict (Φ.S r).fn G).pullC j z) = 0 := by rw [Mor.d_pullC, hz, map_zero]
  have h2 : (Mor.restrict (Φ.S r).fn G).pullC j z ∈ (cx (G ⋙ (Φ.S r).fn)).B j :=
    ((P.cls_surj (cx (G ⋙ (Φ.S r).fn)) j).2.1 _ hpd).1 hx
  have hZ : d Φ.rees j (putr Φ r j z) = 0 := by
    rw [putr_d, hz]; exact putr_zero Φ r _
  have hZ' : d (G ⋙ Φ.rees) j ((Mor.restrict Φ.rees G).pullC j (putr Φ r j z)) = 0 := by
    rw [Mor.d_pullC, hZ, map_zero]
  have h3 : (Mor.restrict Φ.rees G).pull j ((cx Φ.rees).cls _ hZ) = 0 :=
    ((P.cls_surj (cx (G ⋙ Φ.rees)) j).2.1 _ hZ').2 (putr_mem_B (Φ.comap G) r j _ h2)
  have hXZ : d Φ.rees j ((X : ℤ[X]) ^ N • putr Φ r j z) = 0 := by
    rw [map_smul, hZ, smul_zero]
  have h4 := hU.1 _ h3
  rw [← (P.cls_surj (cx Φ.rees) j).2.2.2.2 _ _ hZ hXZ] at h4
  have h5 := cmpS_mem_B Φ (r + N) j _ (((P.cls_surj (cx Φ.rees) j).2.1 _ hXZ).1 h4)
  have e : cmpS Φ (r + N) j ((X : ℤ[X]) ^ N • putr Φ r j z) = (mulSub (Φ.μ ^ N) (Φ.S r) (Φ.S (r + N)) h).pullC j z :=
    inc_inj Φ _ _ (by rw [inc_cmpS, cmp_X_pow', cmp_putr]; rfl)
  rw [e] at h5
  have hμ : d _ j ((mulSub (Φ.μ ^ N) (Φ.S r) (Φ.S (r + N)) h).pullC j z) = 0 := by rw [Mor.d_pullC, hz, map_zero]
  exact ((P.cls_surj (cx (Φ.S (r + N)).fn) j).2.1 _ hμ).2 h5

theorem surj (h0 : ∀ T, (Φ.S 0).S T = ⊤) (hRI : RI ((X : ℤ[X]) ^ N) n Φ.rees G) {j : ℕ} (hj : j ≤ n) (h) (y : H (G ⋙ F) j) :
    ∃ x : H (Φ.S N).fn j, (Mor.restrict (Φ.S N).fn G).pull j x = (mulTo (Φ.μ ^ N) ((Φ.comap G).S N) h).pull j y := by
  have hU : UpTo ((X : ℤ[X]) ^ N) ((Mor.restrict Φ.rees G).pull j) := hRI j hj
  have h0' : ∀ T, ((Φ.comap G).S 0).S T = ⊤ := fun T => h0 (G.obj T)
  obtain ⟨w, hw, rfl⟩ := (P.cls_surj (cx (G ⋙ F)) j).1 y
  have hW : d (G ⋙ Φ.rees) j (put (Φ.comap G) h0' j w) = 0 := by
    refine (put_d (Φ.comap G) h0' j w).trans ?_
    rw [hw]; exact put_zero (Φ.comap G) h0' _
  obtain ⟨x', hx'⟩ := hU.2 ((cx (G ⋙ Φ.rees)).cls (show (cx (G ⋙ Φ.rees)).X j from put (Φ.comap G) h0' j w) hW)
  obtain ⟨Z, hZ, rfl⟩ := (P.cls_surj (cx Φ.rees) j).1 x'
  have hZ' : d (G ⋙ Φ.rees) j ((Mor.restrict Φ.rees G).pullC j Z) = 0 := by
    rw [Mor.d_pullC, hZ, map_zero]
  have hXW : d (G ⋙ Φ.rees) j ((X : ℤ[X]) ^ N • put (Φ.comap G) h0' j w) = 0 := by
    rw [map_smul, hW, smul_zero]
  have hx2 := (P.mapH_cls (Mor.restrict Φ.rees G).hom j Z hZ hZ').symm.trans hx'
  rw [← (P.cls_surj (cx (G ⋙ Φ.rees)) j).2.2.2.2 _ _ hW hXW] at hx2
  have hB := ((P.cls_surj (cx (G ⋙ Φ.rees)) j).2.2.1 _ _ hZ' hXW).1 hx2
  have hc := cmpS_mem_B (Φ.comap G) N j _ hB
  have e : ∀ A : Cn (Φ.comap G).rees j, A = (Mor.restrict Φ.rees G).pullC j Z →
      cmpS (Φ.comap G) N j (A - (X : ℤ[X]) ^ N • put (Φ.comap G) h0' j w) =
        (show Cn ((Φ.comap G).S N).fn j from (Mor.restrict (Φ.S N).fn G).pullC j (cmpS Φ N j Z)) -
          (mulTo (Φ.μ ^ N) ((Φ.comap G).S N) h).pullC j w := by
    intro A hA
    refine inc_inj (Φ.comap G) _ _ ?_
    rw [inc_cmpS, cmp_sub, cmp_X_pow, cmp_put_zero, hA]
    rfl
  have hc' := (e _ rfl) ▸ hc
  have h1 : d (G ⋙ (Φ.S N).fn) j ((Mor.restrict (Φ.S N).fn G).pullC j (cmpS Φ N j Z)) = 0 := by
    rw [Mor.d_pullC, d_cmpS Φ N j Z hZ, map_zero]
  have h2 : d _ j ((mulTo (Φ.μ ^ N) ((Φ.comap G).S N) h).pullC j w) = 0 := by rw [Mor.d_pullC, hw, map_zero]
  exact ⟨(cx (Φ.S N).fn).cls _ (d_cmpS Φ N j Z hZ), ((P.cls_surj (cx ((Φ.comap G).S N).fn) j).2.2.1 _ _ h1 h2).2 hc'⟩

def coef {F₁ : C ⥤ ModuleCat.{w} R} {F₂ : C' ⥤ ModuleCat.{w'} R} (m : Mor F₁ F₂ (RingHom.id R)) : Mor (m.G ⋙ F₁) F₂ (RingHom.id R) :=
  ⟨𝟭 _, m.τ, m.nat⟩

theorem coef_bij {F₁ : C ⥤ ModuleCat.{w} R} {F₂ : C' ⥤ ModuleCat.{w'} R} (m : Mor F₁ F₂ (RingHom.id R))
    (h : ∀ T, Function.Bijective (m.τ T)) (j : ℕ) : Function.Bijective ((coef m).pull j) := by
  have : (coef m).G.IsLeftAdjoint := inferInstanceAs (𝟭 C').IsLeftAdjoint
  exact CrystallineSemistableComparison.P.adj_mor (coef m) h j

theorem coef_res {F₁ : C ⥤ ModuleCat.{w} R} {F₂ : C' ⥤ ModuleCat.{w'} R} (m : Mor F₁ F₂ (RingHom.id R)) (j : ℕ) (x : H F₁ j) :
    m.pull j x = (coef m).pull j ((Mor.restrict F₁ m.G).pull j x) := by
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  rfl

variable {F' : C' ⥤ ModuleCat.{w'} R} (m : Mor F F' (RingHom.id R)) (hm : ∀ T, Function.Bijective (m.τ T)) (S' : ℕ → SubF F')
  (hS : ∀ r T x, m.τ T x ∈ (S' r).S T → x ∈ (Φ.S r).S (m.G.obj T))

include hm hS in
theorem sub_bij (r : ℕ) (h) (T : C') : Function.Bijective ((subMor m (Φ.S r) (S' r) h).τ T) := by
  refine ⟨fun x y e => Subtype.ext ((hm T).1 (congrArg Subtype.val e)), fun y => ?_⟩
  obtain ⟨x, hx⟩ := (hm T).2 y.1
  exact ⟨⟨x, hS r T x (hx ▸ y.2)⟩, Subtype.ext hx⟩

theorem pow_mem (k r : ℕ) (T : C) (x : F.obj T) (hx : x ∈ (Φ.S r).S T) : Φ.μ ^ k • x ∈ (Φ.S (r + k)).S T := by
  induction k with
  | zero => simpa using hx
  | succ k ih => rw [pow_succ', mul_smul]; exact Φ.mul _ T _ ih

theorem key {t μ u : R} (ht : t = μ * u) (N : ℕ) {M : Type w} [AddCommGroup M] [Module R M] (a : M) : t ^ N • a = u ^ N • μ ^ N • a := by
  rw [smul_smul, ht, mul_pow, mul_comm]

include hm hS in
theorem inj' (hRI : RI ((X : ℤ[X]) ^ N) n Φ.rees m.G) {j : ℕ} (hj : j ≤ n) {t u : R} (ht : t = Φ.μ * u) (r : ℕ) (h h')
    (x : H (Φ.S r).fn j) (hx : (subMor m (Φ.S r) (S' r) h).pull j x = 0) :
    (mulSub (t ^ N) (Φ.S r) (Φ.S (r + N)) h').pull j x = 0 := by
  rw [coef_res] at hx
  have h1 := (coef_bij _ (sub_bij Φ m hm S' hS r h) j).1 (hx.trans (map_zero _).symm)
  have h2 := inj Φ m.G hRI hj r (pow_mem Φ N r) x h1
  have e : (mulSub (t ^ N) (Φ.S r) (Φ.S (r + N)) h').pull j x =
      u ^ N • (mulSub (Φ.μ ^ N) (Φ.S r) (Φ.S (r + N)) (pow_mem Φ N r)).pull j x := by
    obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    refine congrArg Submodule.Quotient.mk (Subtype.ext (funext fun s => Subtype.ext ?_))
    exact key ht N (z.1 s).1
  rw [e, h2, smul_zero]

include hm in
theorem surj' (h0 : ∀ T, (Φ.S 0).S T = ⊤) (hRI : RI ((X : ℤ[X]) ^ N) n Φ.rees m.G) {j : ℕ} (hj : j ≤ n) {t u : R}
    (ht : t = Φ.μ * u) (h h') (y : H F' j) :
    ∃ x : H (Φ.S N).fn j, (subMor m (Φ.S N) (S' N) h).pull j x = (mulTo (t ^ N) (S' N) h').pull j y := by
  obtain ⟨y, rfl⟩ := (coef_bij m hm j).2 y
  have hp : ∀ (T : C') (x : (m.G ⋙ F).obj T), Φ.μ ^ N • x ∈ ((Φ.comap m.G).S N).S T := fun T x => by
    have := pow_mem Φ N 0 (m.G.obj T) x (by rw [h0]; trivial)
    rwa [zero_add] at this
  obtain ⟨x, hx⟩ := surj Φ m.G h0 hRI hj hp y
  refine ⟨u ^ N • x, ?_⟩
  rw [map_smul, coef_res]
  refine (congrArg (fun a => u ^ N • (coef (subMor m (Φ.S N) (S' N) h)).pull j a) hx).trans ?_
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  refine congrArg Submodule.Quotient.mk (Subtype.ext (funext fun s => Subtype.ext ?_))
  exact (congrArg (u ^ N • ·) (map_smul (m.τ _) (Φ.μ ^ N) (z.1 s))).trans (key ht N _).symm

end CrystallineSemistableComparison.HT.Rees

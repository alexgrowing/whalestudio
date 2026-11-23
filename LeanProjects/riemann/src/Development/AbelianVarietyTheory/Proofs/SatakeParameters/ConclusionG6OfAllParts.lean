import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.HeckeCharEqOfLAdicRealisation
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsHeckeGaloisQOfIsHeckeGalois

noncomputable section

namespace GlobalTheory.EigenPoint

open Formalism.BasicNotions Formalism.ConjugateSelfDual Formalism.MainNotions Formalism.MainNotions.N Polynomial NumberField IsDedekindDomain ReciprocityTheory.Gal GlobalTheory.StringRepresentationDecomposition

section Alg

variable {Γ : Type} [Group Γ] {K : Type} [Field K]

theorem charpoly_smul [CharZero K] {n : ℕ} (M : Matrix (Fin n) (Fin n) K) {c : K} (hc : c ≠ 0) :
    (c • M).charpoly = M.charpoly.scaleRoots c := by
  have : Infinite K := Infinite.of_injective (Nat.cast : ℕ → K) Nat.cast_injective
  apply Polynomial.funext
  intro x
  obtain ⟨y, rfl⟩ : ∃ y, x = c * y := ⟨c⁻¹ * x, by rw [← mul_assoc, mul_inv_cancel₀ hc, one_mul]⟩
  rw [scaleRoots_eval_mul, Matrix.charpoly_natDegree_eq_dim, Matrix.eval_charpoly, Matrix.eval_charpoly,
    ← Matrix.det_smul, smul_sub]
  congr 2
  ext a b
  simp only [Matrix.smul_apply, Matrix.scalar_apply, Matrix.diagonal_apply, smul_eq_mul]
  split_ifs <;> simp

theorem twGL_val {a : ℕ} (ρ : Γ →* GL (Fin a) K) (χ : Γ →* Kˣ) (g : Γ) :
    ((Formalism.MainNotions.SumRepresentations.At.twGL ρ χ g : GL _ K) : Matrix (Fin a) (Fin a) K) =
      (χ g : K) • ((ρ g : GL _ K) : Matrix (Fin a) (Fin a) K) := by
  show algebraMap K (Matrix (Fin a) (Fin a) K) (χ g : K) * ((ρ g : GL _ K) : Matrix (Fin a) (Fin a) K) = _
  rw [Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul]

theorem isInv_twGL {a : ℕ} (ρ : Γ →* GL (Fin a) K) (χ : Γ →* Kˣ) (W : Submodule K (Fin a → K)) :
    IsInv (Formalism.MainNotions.SumRepresentations.At.twGL ρ χ) W ↔ IsInv ρ W := by
  constructor
  · intro h g v hv
    have := W.smul_mem ((χ g : K)⁻¹) (h g v hv)
    rwa [twGL_val, Matrix.smul_mulVec, smul_smul, inv_mul_cancel₀ (Units.ne_zero _), one_smul] at this
  · intro h g v hv
    rw [twGL_val, Matrix.smul_mulVec]
    exact W.smul_mem _ (h g v hv)

theorem ss_twGL {a : ℕ} (ρ : Γ →* GL (Fin a) K) (χ : Γ →* Kˣ) (h : IsSSRep ρ) :
    IsSSRep (Formalism.MainNotions.SumRepresentations.At.twGL ρ χ) := fun W hW => by
  obtain ⟨W', hW', hc⟩ := h W ((isInv_twGL ρ χ W).1 hW)
  exact ⟨W', (isInv_twGL ρ χ W').2 hW', hc⟩

end Alg

theorem ms_one {s : Multiset ℕ} (h : s.sum = 1) (h1 : ∀ a ∈ s, 1 ≤ a) : s = {1} := by
  have hne : s ≠ 0 := by rintro rfl; simp at h
  have hc := Multiset.card_nsmul_le_sum h1
  have hp := Multiset.card_pos.2 hne
  rw [smul_eq_mul, mul_one, h] at hc
  have hc1 : Multiset.card s = 1 := by omega
  obtain ⟨a, rfl⟩ := Multiset.card_eq_one.1 hc1
  simp only [Multiset.sum_singleton] at h
  rw [h]

theorem sum_split {M : Type} [AddCommMonoid M] {n m : ℕ} (h : n = m + 1) (f : Fin n → M) :
    ∑ k, f k = ∑ k : Fin m, f (Fin.cast h.symm k.castSucc) + f (Fin.cast h.symm (Fin.last m)) := by
  subst h
  simp [Fin.sum_univ_castSucc]

theorem prod_flatMap' {α M : Type} [CommMonoid M] (l : List α) (f : α → List M) :
    (l.flatMap f).prod = (l.map fun a => (f a).prod).prod := by
  induction l with
  | nil => simp
  | cons a l ih => simp [List.flatMap_cons, List.prod_append, ih]

theorem prod_flat {M : Type} [CommMonoid M] (n : ℕ) (d : Fin n → ℕ) (f : Fin n → ℕ → M) :
    (((List.finRange n).map fun k => ((List.range (d k)).map (f k)).prod)).prod =
      ∏ k, ∏ a ∈ Finset.range (d k), f k a := by
  rw [Fin.prod_univ_def]
  congr 1

variable (D : D7) (i : D.nd.Loc)

def eU : G D.host.E D.nd.Om →* (Qbar (D.nd.l i))ˣ :=
  (Units.map (iotaOQ D.nd D.naut i).toMonoidHom).comp (Formalism.MainNotions.N.Glob.epsO D.nd i)

def cU : G D.host.E D.nd.Om →* (Qbar (D.nd.l i))ˣ :=
  (Units.map (iotaOQ D.nd D.naut i).toMonoidHom).comp (D.nd.chi i 1)

theorem eU_pow (g : G D.host.E D.nd.Om) (a : ℕ) :
    ((((eU D i)⁻¹ ^ a) g : (Qbar (D.nd.l i))ˣ) : Qbar (D.nd.l i)) = (epsQ D i g)⁻¹ ^ a := by
  rw [MonoidHom.pow_apply, MonoidHom.inv_apply, Units.val_pow_eq_pow_val, Units.val_inv_eq_inv_val]
  rfl

def twList (Pa : List (Part D.naut.CG))
    (R : ∀ k : Fin Pa.length, G D.host.E D.nd.Om →* GL (Fin (Pa.get k).a) (Qbar (D.nd.l i))) :
    List (Σ m : ℕ, G D.host.E D.nd.Om →* GL (Fin m) (Qbar (D.nd.l i))) :=
  (List.finRange Pa.length).flatMap fun k =>
    (List.range (Pa.get k).d).map fun a => ⟨(Pa.get k).a, Formalism.MainNotions.SumRepresentations.At.twGL (R k) ((eU D i)⁻¹ ^ a)⟩

theorem mem_twList {Pa : List (Part D.naut.CG)}
    {R : ∀ k : Fin Pa.length, G D.host.E D.nd.Om →* GL (Fin (Pa.get k).a) (Qbar (D.nd.l i))}
    {p : Σ m : ℕ, G D.host.E D.nd.Om →* GL (Fin m) (Qbar (D.nd.l i))} (hp : p ∈ twList D i Pa R) :
    ∃ k : Fin Pa.length, ∃ a < (Pa.get k).d,
      p = ⟨(Pa.get k).a, Formalism.MainNotions.SumRepresentations.At.twGL (R k) ((eU D i)⁻¹ ^ a)⟩ := by
  obtain ⟨k, -, hk⟩ := List.mem_flatMap.1 hp
  obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hk
  exact ⟨k, a, List.mem_range.1 ha, rfl⟩

theorem twList_cp (Pa : List (Part D.naut.CG))
    (R : ∀ k : Fin Pa.length, G D.host.E D.nd.Om →* GL (Fin (Pa.get k).a) (Qbar (D.nd.l i)))
    (g : G D.host.E D.nd.Om) :
    ((twList D i Pa R).map fun p => ((p.2 g : GL _ _) : Matrix (Fin p.1) (Fin p.1) (Qbar (D.nd.l i))).charpoly).prod =
      ∏ k : Fin Pa.length, ∏ a ∈ Finset.range (Pa.get k).d,
        (((R k g : GL _ _) : Matrix (Fin (Pa.get k).a) (Fin (Pa.get k).a) (Qbar (D.nd.l i))).charpoly).scaleRoots
          ((epsQ D i g)⁻¹ ^ a) := by
  rw [twList, List.map_flatMap, prod_flatMap']
  simp only [List.map_map, Function.comp_def]
  rw [prod_flat]
  refine Finset.prod_congr rfl fun k _ => Finset.prod_congr rfl fun a _ => ?_
  rw [twGL_val, charpoly_smul _ (Units.ne_zero _), eU_pow]

theorem twList_ss (Pa : List (Part D.naut.CG))
    (R : ∀ k : Fin Pa.length, G D.host.E D.nd.Om →* GL (Fin (Pa.get k).a) (Qbar (D.nd.l i)))
    (hR : ∀ k, IsStringRep D i (Pa.get k) (R k)) : ∀ p ∈ twList D i Pa R, IsSSRep p.2 := by
  intro p hp
  obtain ⟨k, a, -, rfl⟩ := mem_twList D i hp
  exact ss_twGL _ _ (hR k).2.1

theorem mapRep_val {Γ A B : Type} [Group Γ] [CommRing A] [CommRing B] {a : ℕ} (f : A →+* B)
    (ρ : Γ →* GL (Fin a) A) (g : Γ) :
    ((mapRep f ρ g : GL _ _) : Matrix (Fin a) (Fin a) B) = ((ρ g : GL _ _) : Matrix (Fin a) (Fin a) A).map f := rfl

theorem eig_map (r : G D.host.E D.nd.Om →* GL (Fin D.R.nV) (D.nd.O i)) (v : Fin D.R.nV → Kf D.nd i)
    (hv0 : v ≠ 0) (hv : ∀ g, ((mapRep (algebraMap (D.nd.O i) (Kf D.nd i)) r g : GL _ _) :
        Matrix (Fin D.R.nV) (Fin D.R.nV) (Kf D.nd i)).mulVec v =
          algebraMap (D.nd.O i) (Kf D.nd i) (chi1 D.nd i g) • v) :
    ∃ w : Fin D.R.nV → Qbar (D.nd.l i), w ≠ 0 ∧ ∀ g,
      ((mapRep (iotaOQ D.nd D.naut i) r g : GL _ _) : Matrix (Fin D.R.nV) (Fin D.R.nV) (Qbar (D.nd.l i))).mulVec w =
        ((cU D i g : (Qbar (D.nd.l i))ˣ) : Qbar (D.nd.l i)) • w := by
  refine ⟨fun j => D.naut.iotaQ i (v j), fun h => hv0 (funext fun j => ?_), fun g => funext fun j => ?_⟩
  · have := congrFun h j
    exact (D.naut.iotaQ i).injective (by simpa using this)
  · have e1 := congrArg (D.naut.iotaQ i) (congrFun (hv g) j)
    rw [RingHom.map_mulVec, mapRep_val] at e1
    rw [mapRep_val]
    refine e1.trans ?_
    rw [Pi.smul_apply, smul_eq_mul, map_mul, Pi.smul_apply, smul_eq_mul]
    rfl

theorem part_eq (h3 : HeckeCharEqOfLAdicRealisation) (h4 : MuChar) (hA : Formalism.MainNotions.SumRepresentations.admitted D) (hg : HG D.nd D.naut i)
    (p : Part D.naut.CG) (Rk : G D.host.E D.nd.Om →* GL (Fin p.a) (Qbar (D.nd.l i)))
    (hR : IsStringRep D i p Rk) (ha : p.a = 1) (hd : p.d = D.R.t) (u : Fin p.a → Qbar (D.nd.l i)) (hu0 : u ≠ 0)
    (hu : ∀ g, ((Rk g : GL _ _) : Matrix (Fin p.a) (Fin p.a) (Qbar (D.nd.l i))).mulVec u =
      iotaOQ D.nd D.naut i (chi1 D.nd i g) • u) :
    p = ⟨1, D.naut.tw (D.naut.muC i) D.naut.etaTinv, D.R.t⟩ := by
  rcases p with ⟨a, π, d⟩
  dsimp only at ha hd
  subst ha hd
  have hu00 : u 0 ≠ 0 := fun h => hu0 (funext fun j => by rw [Fin.fin_one_eq_zero j]; exact h)
  have h00 : ∀ g, ((Rk g : GL _ _) : Matrix (Fin 1) (Fin 1) (Qbar (D.nd.l i))) 0 0 =
      iotaOQ D.nd D.naut i (chi1 D.nd i g) := fun g => by
    have := congrFun (hu g) 0
    simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_one, Pi.smul_apply, smul_eq_mul] at this
    exact mul_right_cancel₀ hu00 this
  have hπ := h3 D hA i π (D.naut.tw (D.naut.muC i) D.naut.etaTinv) _ Rk hR.2.2 (h4 D hA i hg Rk h00)
  subst hπ
  rfl

theorem mem_ZN (h1 : CentredStringDecomposition) (h2 : PurityStringWeight) (h3 : HeckeCharEqOfLAdicRealisation) (h4 : MuChar) (h8 : EigenCharTwist)
    (hrc : ResCount) (h11 : Numerics) (hA : Formalism.MainNotions.SumRepresentations.admitted D) (hRb : RbEx D) (hg : HG D.nd D.naut i) (r : D.nd.X i → (G D.host.E D.nd.Om →* GL (Fin D.R.nV) (D.nd.O i)))
    (hr : GoodR D.nd i r) (x : D.nd.X i) (v : Fin D.R.nV → Kf D.nd i) (hv0 : v ≠ 0)
    (hv : ∀ g, ((mapRep (algebraMap (D.nd.O i) (Kf D.nd i)) (r x) g : GL _ _) :
        Matrix (Fin D.R.nV) (Fin D.R.nV) (Kf D.nd i)).mulVec v =
          algebraMap (D.nd.O i) (Kf D.nd i) (chi1 D.nd i g) • v) :
    x ∈ ZN D.nd D.naut i := by
  obtain ⟨P, hP⟩ := D.naut.pt_surj i x
  obtain ⟨Pa, hBC⟩ := hA.1.1.2.2.1 i P
  obtain ⟨R, hR, hcp⟩ := h1 D hA i x P Pa hP hBC r hr
  obtain ⟨Ak, hAk, hsum⟩ := hrc D hA hRb i hg r hr x Pa R hR hcp
  have hss : IsSSRep (mapRep (iotaOQ D.nd D.naut i) (r x)) :=
    (GlobalTheory.NRows.isHeckeGaloisQ_of_isHeckeGalois D i x (r x) (hr x)).2.1
  obtain ⟨p, hpL, u, hu0, hu⟩ := h8 (Qbar (D.nd.l i)) (G D.host.E D.nd.Om) D.R.nV
    (mapRep (iotaOQ D.nd D.naut i) (r x)) (twList D i Pa R) (cU D i) hss (twList_ss D i Pa R hR)
    (fun g => (hcp g).trans (twList_cp D i Pa R g).symm) (eig_map D i (r x) v hv0 hv)
  obtain ⟨k, a, ha, rfl⟩ := mem_twList D i hpL
  have hW : ∀ g, ((epsQ D i g)⁻¹ ^ a) • ((R k g : GL _ _) : Matrix (Fin (Pa.get k).a) (Fin (Pa.get k).a)
      (Qbar (D.nd.l i))).mulVec u = iotaOQ D.nd D.naut i (chi1 D.nd i g) • u := fun g => by
    have e := hu g
    rw [twGL_val, Matrix.smul_mulVec, eU_pow] at e
    exact e
  have hwt := h2 D hA i x P Pa hP hBC k (R k) (hR k) a ha ⟨u, hu0, hW⟩
  have hmem : Pa.get k ∈ Pa := List.get_mem Pa k
  have ha1 : 1 ≤ (Pa.get k).a := (hBC.1 _ hmem).1
  have hr1 : 1 < D.R.r := by
    have := D.R.two_le_m; have := D.R.m_add_three_le_k
    show 1 < D.R.k + D.R.m - 1
    omega
  have ht2 : 2 ≤ D.R.t := by
    have := D.R.two_le_m; have := D.R.m_add_three_le_k; have := D.R.rank_add_five_le
    omega
  have hle : (Pa.get k).d • Ak k ≤ D.R.r ::ₘ Multiset.replicate D.R.t 1 := by
    rw [← hsum, ← Finset.add_sum_erase _ _ (Finset.mem_univ k)]
    exact Multiset.le_add_right _ _
  have hnum := h11 D.R.r D.R.t (Pa.get k).d (Pa.get k).a a (Ak k) hr1 ht2 ha hwt (hAk k).1 (hAk k).2 ha1 hle
  have ha0 : a = 0 := by rw [hnum.2] at hwt; omega
  subst ha0
  have hpart := part_eq D i h3 h4 hA hg (Pa.get k) (R k) (hR k) hnum.1 hnum.2 u hu0
    (fun g => by simpa using hW g)
  exact ⟨P, hP, Pa, hBC, hpart ▸ hmem⟩

theorem cusp_of (h1 : CentredStringDecomposition) (hrc : ResCount)
    (h12 : Rest) (hA : Formalism.MainNotions.SumRepresentations.admitted D) (hRb : RbEx D) (hg : HG D.nd D.naut i)
    (r : D.nd.X i → (G D.host.E D.nd.Om →* GL (Fin D.R.nV) (D.nd.O i))) (hr : GoodR D.nd i r) (x : D.nd.X i)
    (Sig : List (Part D.naut.CG)) (hSig : HasParamX D.nd D.naut i x Sig) : IsCuspIso D.nd D.naut Sig := by
  obtain ⟨P, hP, hBC⟩ := hSig
  have hlen : (twistIso D.nd D.naut (Sig ++ [muPart D.nd D.naut i]) D.naut.etaTinv).length = Sig.length + 1 := by
    simp [twistIso]
  have hlast : (twistIso D.nd D.naut (Sig ++ [muPart D.nd D.naut i]) D.naut.etaTinv).get
      (Fin.cast hlen.symm (Fin.last _)) = ⟨1, D.naut.tw (D.naut.muC i) D.naut.etaTinv, D.R.t⟩ := by
    simp only [List.get_eq_getElem, Fin.val_cast, Fin.val_last]
    simp [twistIso, muPart, List.getElem_append_right]
  generalize hPa : twistIso D.nd D.naut (Sig ++ [muPart D.nd D.naut i]) D.naut.etaTinv = Pa at hBC hlen hlast
  obtain ⟨R, hR, hcp⟩ := h1 D hA i x P Pa hP hBC r hr
  obtain ⟨Ak, hAk, hsum⟩ := hrc D hA hRb i hg r hr x Pa R hR hcp
  rw [sum_split hlen] at hsum
  have hAl : Ak (Fin.cast hlen.symm (Fin.last _)) = {1} :=
    ms_one ((hAk _).1.trans (by rw [hlast])) (hAk _).2
  have hlt : (Pa.get (Fin.cast hlen.symm (Fin.last _))).d • Ak (Fin.cast hlen.symm (Fin.last _)) =
      Multiset.replicate D.R.t 1 := by
    rw [hAl, hlast]
    exact Multiset.nsmul_singleton _ _
  rw [hlt, ← Multiset.singleton_add] at hsum
  have hS := add_right_cancel hsum
  have hmem : ∀ k : Fin Sig.length, Pa.get (Fin.cast hlen.symm k.castSucc) ∈ Pa := fun k => List.get_mem _ _
  have hG := h12 (Fin Sig.length) (fun k => (Pa.get (Fin.cast hlen.symm k.castSucc)).d)
    (fun k => Ak (Fin.cast hlen.symm k.castSucc)) D.R.r (fun k => (hBC.1 _ (hmem k)).2.1)
    (fun k h => by
      have e := (hAk (Fin.cast hlen.symm k.castSucc)).1
      rw [h, Multiset.sum_zero] at e
      have := (hBC.1 _ (hmem k)).1
      omega) hS
  have hl1 : Sig.length = 1 := by simpa using hG.1
  obtain ⟨p, rfl⟩ := List.length_eq_one_iff.1 hl1
  have h0 := hG.2 ⟨0, by simp⟩
  have hget : Pa.get (Fin.cast hlen.symm (Fin.castSucc (⟨0, by simp⟩ : Fin [p].length))) =
      ⟨p.a, D.naut.tw p.π D.naut.etaTinv, p.d⟩ := by
    subst hPa
    simp [twistIso]
  have hd : p.d = 1 := by have := h0.1; rw [hget] at this; exact this
  have ha : p.a = D.R.r := by
    have e := (hAk (Fin.cast hlen.symm (Fin.castSucc (⟨0, by simp⟩ : Fin [p].length)))).1
    rw [h0.2, hget, Multiset.sum_singleton] at e
    exact e.symm
  rcases p with ⟨a, π, d⟩
  dsimp only at hd ha
  subst hd ha
  exact ⟨π, rfl⟩

theorem mem_Z_and_cusp_of_steps : CentredStringDecomposition → PurityStringWeight → HeckeCharEqOfLAdicRealisation → MuChar → EigenCharTwist → ResCount → Numerics → Rest →
    ∀ D : D7, SumRepresentations.admitted D → RbEx D → SumRepresentations.ConclusionG6 D :=
  fun h1 h2 h3 h4 h8 hrc h11 h12 D hA hRb i hg r hr x hx =>
    ⟨hx.elim fun v hv => mem_ZN D i h1 h2 h3 h4 h8 hrc h11 hA hRb hg r hr x v hv.1 hv.2,
      fun Sig hSig => cusp_of D i h1 hrc h12 hA hRb hg r hr x Sig hSig⟩

end GlobalTheory.EigenPoint

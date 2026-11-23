import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HasPRatio
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MultiplicationLatticeSecond
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SuccessiveMinimaPositiveNorms

open AlgebraicGeometry CategoryTheory Limits NumberField MonObj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM GlobalTheory.ShFam.Pad GlobalTheory.HTLine
open Formalism.MainNotions.DIV.Cons (intO SCF)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.HTLine.GrMinor

open GlobalTheory.LineNorm

theorem exists_ne {L : Type} [Field L] {g J : ℕ} (h : Fin J → Fin g → L)
    (hh : ∀ c : Fin g → L, (∀ j, ∑ i, h j i * c i = 0) → c = 0) {m : ℕ} (a : Fin m → Fin g → L)
    (ha : LinearIndependent L a) {k : ℕ} (hk : k ≤ m) :
    ∃ σ : Fin k → Fin J, ∑ s : Fin k → Fin g, (∏ i, h (σ i) (s i)) * minor a hk s ≠ 0 := by
  let G : Matrix (Fin J) (Fin m) L := Matrix.of fun j l => ∑ t, h j t * a l t
  have hli : LinearIndependent L G.transpose := by
    have hker : LinearMap.ker (Matrix.mulVecLin (Matrix.of h)) = ⊥ :=
      LinearMap.ker_eq_bot'.mpr fun c hc => hh c fun j => congrFun hc j
    exact ha.map' _ hker
  obtain ⟨κ, u, b, -, hu0, hu1, hb, hbd, hc⟩ := GlobalTheory.LineNorm.Covol.exists_pivot (⊤ : ValuationSubring L) G hli
  refine ⟨κ ∘ Fin.castLE hk, ?_⟩
  rw [GlobalTheory.LineNorm.Covol.sum_prod_mul_minor (fun i => h ((κ ∘ Fin.castLE hk) i)) a hk, ← Matrix.det_transpose]
  change (G.submatrix (κ ∘ Fin.castLE hk) (Fin.castLE hk)).det ≠ 0
  rw [hc, GlobalTheory.LineNorm.Covol.det_eq u b hb hk]
  have hMt : (u.submatrix (κ ∘ Fin.castLE hk) (Fin.castLE hk)).BlockTriangular OrderDual.toDual :=
    fun i j hij => hu0 _ _ hij
  rw [Matrix.det_of_isLowerTriangular _ hMt]
  refine mul_ne_zero ?_ (Finset.prod_ne_zero_iff.mpr fun l _ => hbd _)
  simp [hu1]

theorem sep_of_span {R S : Type} [CommRing R] [Field S] (ψ : R →+* S) (p : ℕ) (hp : (p : S) ≠ 0) {g J : ℕ}
    (h : Fin J → Fin g → R) (N : ℕ) (hN : ∀ i, Pi.single i ((p : R) ^ N) ∈ Submodule.span R (Set.range h))
    (c : Fin g → S) (hc : ∀ j, ∑ i, ψ (h j i) * c i = 0) : c = 0 := by
  have key : ∀ v ∈ Submodule.span R (Set.range h), ∑ i, ψ (v i) * c i = 0 := by
    intro v hv
    induction hv using Submodule.span_induction with
    | mem x hx => obtain ⟨j, rfl⟩ := hx; exact hc j
    | zero => simp
    | add x y _ _ hx hy => simp [add_mul, Finset.sum_add_distrib, hx, hy]
    | smul r x _ hx =>
      calc ∑ i, ψ ((r • x) i) * c i = ψ r * ∑ i, ψ (x i) * c i := by
            rw [Finset.mul_sum]
            exact Finset.sum_congr rfl fun i _ => by simp <;> ring
        _ = 0 := by rw [hx, mul_zero]
  funext i
  have h1 := key _ (hN i)
  rw [Finset.sum_eq_single i (fun b _ hb => by simp [Pi.single_eq_of_ne hb]) (by simp)] at h1
  simpa [hp] using h1

theorem norm_eq_iSup {κ : Type} [Fintype κ] [Nonempty κ] {S : Type} [NormedField S] (f : κ → S) :
    ‖f‖ = ⨆ i, ‖f i‖ := by
  refine le_antisymm ((pi_norm_le_iff_of_nonneg ?_).2 fun i => le_ciSup (f := fun i => ‖f i‖) (Finite.bddAbove_range _) i)
    (ciSup_le fun i => norm_le_pi_norm f i)
  exact (norm_nonneg (f (Classical.arbitrary κ))).trans (le_ciSup (f := fun i => ‖f i‖) (Finite.bddAbove_range _) _)

theorem map_minor {R S : Type} [CommRing R] [CommRing S] (ψ : R →+* S) {m g k : ℕ} (a : Fin m → Fin g → R)
    (hk : k ≤ m) (s : Fin k → Fin g) : ψ (minor a hk s) = minor (fun l i => ψ (a l i)) hk s := by
  unfold minor
  rw [RingHom.map_det]
  rfl

end GlobalTheory.HTLine.GrMinor

namespace GlobalTheory.HTLine.GrMinor

open GlobalTheory.LineNorm GlobalTheory.LieMet ReciprocityTheory.ChartRestriction.G.PullbackSections

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {X : Scheme.{0}}
  {t : SAB H X}

theorem comb_eq {S : Type} [CommRing S] {x : Sp S ⟶ X} {m : ℕ} {u : Fin m → (Sp (DualNumber S) ⟶ t.G.left)}
    (hu : ∀ i, IsTanAtG t x (u i)) (a : Fin m → S) (w : Sp (DualNumber S) ⟶ t.G.left) :
    IsCombAtG t x u a w ↔ w = (tv (∑ i, a i • tanOf (hu i))).left := by
  have h0 : IsCombAtG t x u a (tv (∑ i, a i • tanOf (hu i))).left := (isComb_iff (fun i => tanOf (hu i)) a _).2 rfl
  refine ⟨fun h => ?_, fun h => h ▸ h0⟩
  obtain ⟨v, hv, e⟩ := h
  obtain ⟨v', hv', e'⟩ := h0
  have : v = v' := funext fun i => Over.OverMorphism.ext ((hv i).trans (hv' i).symm)
  rw [← e, ← e', this]

theorem comb_comb {S : Type} [CommRing S] {x : Sp S ⟶ X} {g m : ℕ} {e : Fin g → (Sp (DualNumber S) ⟶ t.G.left)}
    (he : ∀ i, IsTanAtG t x (e i)) {w : Fin m → (Sp (DualNumber S) ⟶ t.G.left)} (hw : ∀ j, IsTanAtG t x (w j))
    (a : Fin m → Fin g → S) (ha : ∀ j, IsCombAtG t x e (a j) (w j)) (cf : Fin m → S)
    (v : Sp (DualNumber S) ⟶ t.G.left) :
    IsCombAtG t x w cf v ↔ IsCombAtG t x e (fun r => ∑ l, cf l * a l r) v := by
  have hW : ∀ j, tanOf (hw j) = ∑ r, a j r • tanOf (he r) := fun j => tan_ext ((comb_eq he _ _).1 (ha j))
  rw [comb_eq hw, comb_eq he]
  have : ∑ l, cf l • tanOf (hw l) = ∑ r, (∑ l, cf l * a l r) • tanOf (he r) := by
    simp only [hW, Finset.smul_sum, smul_smul, Finset.sum_smul]
    exact Finset.sum_comm
  rw [this]

theorem linIndep_of_ind {k : Type} [Field k] {x : Sp k ⟶ X} {g m : ℕ} {e : Fin g → (Sp (DualNumber k) ⟶ t.G.left)}
    (he : ∀ i, IsTanAtG t x (e i)) {w : Fin m → (Sp (DualNumber k) ⟶ t.G.left)} (hw : Pull.Ind t x w)
    (a : Fin m → Fin g → k) (ha : ∀ j, IsCombAtG t x e (a j) (w j)) : LinearIndependent k a := by
  rw [Fintype.linearIndependent_iff]
  intro c hc
  have h0 : ∀ r, ∑ l, c l * a l r = ∑ l, (0 : Fin m → k) l * a l r := fun r => by
    have := congrFun hc r
    simpa [Finset.sum_apply] using this
  have h1 : IsCombAtG t x w c (tv (∑ l, c l • tanOf (hw.1 l))).left := (comb_eq hw.1 _ _).2 rfl
  have h2 : IsCombAtG t x w 0 (tv (∑ l, c l • tanOf (hw.1 l))).left := by
    rw [comb_comb he hw.1 a ha] at h1 ⊢
    rw [show (fun r => ∑ l, c l * a l r) = (fun r => ∑ l, (0 : Fin m → k) l * a l r) from funext h0] at h1
    exact h1
  exact congrFun (hw.2 _ _ _ h1 h2)

theorem coords {R : Type} [CommRing R] {x : Sp R ⟶ X} {g : ℕ} {e : Fin g → (Sp (DualNumber R) ⟶ t.G.left)}
    (he : IsTanBasis t x e) {m : ℕ} {w : Fin m → (Sp (DualNumber R) ⟶ t.G.left)} (hw : ∀ j, IsTanAtG t x (w j)) :
    ∃ a : Fin m → Fin g → R, ∀ j, IsCombAtG t x e (a j) (w j) := by
  have h1 : spMap (RingHom.id R) = 𝟙 _ := Spec.map_id _
  have h2 : dualMap (RingHom.id R) = RingHom.id _ := by
    refine RingHom.ext fun z => ?_
    ext <;> simp [dualMap]
  have h3 : spMap (dualMap (RingHom.id R)) = 𝟙 _ := by rw [h2]; exact Spec.map_id _
  have h := he.2 R (RingHom.id R)
  simp only [h1, h3, Category.id_comp] at h
  choose a ha using fun j => (h (w j) (hw j)).exists
  exact ⟨a, ha⟩

end GlobalTheory.HTLine.GrMinor

namespace GlobalTheory.HTLine.GrMinor

open GlobalTheory.LineNorm GlobalTheory.LieMet

theorem grNorm_eq_ratio : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (X : Scheme.{0}) (t : SAB H X) (R : Type) [CommRing R] (x : Sp R ⟶ X) (p : ℕ) (b : Bool) (g M : ℕ) (e : Fin g → (Sp (DualNumber R) ⟶ t.G.left)) (h : Fin (M + 1) → Fin g → R), p.Prime → GlobalTheory.LineNorm.IsTanBasis t x e → Pres t x p b e h → ∀ (m : ℕ) (w : Fin m → (Sp (DualNumber R) ⟶ t.G.left)), (∀ j, IsTanAtG t x (w j)) → (∀ (k : Type) [Field k] (ψ : R →+* k), (p : k) ≠ 0 → Pull.Ind t (spMap ψ ≫ x) (fun j => spMap (dualMap ψ) ≫ w j)) → ∀ i : Fin m, ∃ (a a' : ℕ) (A : Fin a → R) (B : Fin a' → R), (p : R) ∈ (Ideal.span (Set.range A)).radical ∧ (p : R) ∈ (Ideal.span (Set.range B)).radical ∧ ∀ (C : SCF p) (φ : R →+* ↥(intO ↥C.S)), GlobalTheory.ShFam.Pad.grNorm t (spMap (intO ↥C.S).subtype ≫ spMap φ ≫ x) (lat t p (spMap (intO ↥C.S).subtype ≫ spMap φ ≫ x) b) (fun j => spMap (dualMap ((intO ↥C.S).subtype.comp φ)) ≫ w j) i * ‖fun j => ((φ (B j) : ↥(intO ↥C.S)) : ↥C.S)‖ = ‖fun j => ((φ (A j) : ↥(intO ↥C.S)) : ↥C.S)‖ := by
  intro E _ _ _ H X t R _ x p b g M e h hp he hP m w hw hind i
  obtain ⟨a, ha⟩ := coords he hw
  obtain ⟨N, hN⟩ := hP.1
  let F : ∀ k, k ≤ m → (Fin k → Fin (M + 1)) → R := fun k hk σ =>
    ∑ s : Fin k → Fin g, (∏ l, h (σ l) (s l)) * minor a hk s
  have hrad : ∀ k (hk : k ≤ m),
      (p : R) ∈ (Ideal.span (Set.range fun j => F k hk ((Fintype.equivFin _).symm j))).radical := by
    intro k hk
    rw [Ideal.radical_eq_sInf, Submodule.mem_sInf]
    rintro (P : Ideal R) ⟨hle, hPr⟩
    by_contra hpP
    haveI := hPr
    have hp0 : ((p : ℕ) : P.ResidueField) ≠ 0 := by
      rw [← map_natCast (algebraMap R P.ResidueField)]
      exact fun h0 => hpP (Ideal.algebraMap_residueField_eq_zero.1 h0)
    have hI := hind P.ResidueField (algebraMap R P.ResidueField) hp0
    have he' : ∀ r, IsTanAtG t (spMap (algebraMap R P.ResidueField) ≫ x)
        (spMap (dualMap (algebraMap R P.ResidueField)) ≫ e r) := fun r => isTan_map _ rfl (he.1 r)
    have ha' := fun j => GlobalTheory.LatDRFree.comb_map t (algebraMap R P.ResidueField) (ha j)
    have hli := linIndep_of_ind he' hI _ ha'
    obtain ⟨σ, hσ⟩ := exists_ne (fun j r => algebraMap R P.ResidueField (h j r))
      (sep_of_span _ p hp0 h N hN) _ hli hk
    apply hσ
    have hmem : F k hk σ ∈ P := hle (Ideal.subset_span ⟨Fintype.equivFin _ σ, by simp⟩)
    calc _ = algebraMap R P.ResidueField (F k hk σ) := by
          simp only [F, map_sum, map_mul, map_prod, map_minor]
      _ = 0 := Ideal.algebraMap_residueField_eq_zero.2 hmem
  refine ⟨_, _, fun j => F (i + 1) (Nat.succ_le_of_lt i.2) ((Fintype.equivFin _).symm j),
    fun j => F i i.2.le ((Fintype.equivFin _).symm j), hrad _ _, hrad _ _, fun C φ => ?_⟩
  set ψ : R →+* ↥C.S := (intO ↥C.S).subtype.comp φ with hψ
  have hx : spMap ψ ≫ x = spMap (intO ↥C.S).subtype ≫ spMap φ ≫ x := by
    rw [← Category.assoc, ← Spec.map_comp]
    rfl
  have hp0 : ((p : ℕ) : ↥C.S) ≠ 0 := Nat.cast_ne_zero.2 hp.ne_zero
  have he' : ∀ r, IsTanAtG t (spMap (intO ↥C.S).subtype ≫ spMap φ ≫ x) (spMap (dualMap ψ) ≫ e r) :=
    fun r => isTan_map ψ hx (he.1 r)
  have hw' : ∀ l, IsTanAtG t (spMap (intO ↥C.S).subtype ≫ spMap φ ≫ x) (spMap (dualMap ψ) ≫ w l) :=
    fun l => isTan_map ψ hx (hw l)
  have ha' : ∀ l, IsCombAtG t (spMap (intO ↥C.S).subtype ≫ spMap φ ≫ x) (fun r => spMap (dualMap ψ) ≫ e r)
      (fun r => ψ (a l r)) (spMap (dualMap ψ) ≫ w l) := fun l => hx ▸ GlobalTheory.LatDRFree.comb_map t ψ (ha l)
  have hI := hind ↥C.S ψ hp0
  rw [hx] at hI
  have hli := linIndep_of_ind he' hI _ ha'
  have hsep := sep_of_span ψ p hp0 h N hN
  let Nf : Fin m → ℝ := fun l => grNorm t (spMap (intO ↥C.S).subtype ≫ spMap φ ≫ x)
    (lat t p (spMap (intO ↥C.S).subtype ≫ spMap φ ≫ x) b) (fun j => spMap (dualMap ψ) ≫ w j) l
  have hset : ∀ l, Nf l = sInf {r | ∃ cf : Fin m → ↥C.S, cf l ≠ 0 ∧ (∀ l', l < l' → cf l' = 0) ∧
      (∀ j, ‖∑ i, ψ (h j i) * ∑ l', cf l' * ψ (a l' i)‖ ≤ 1) ∧ r = ‖cf l‖⁻¹} := by
    intro l
    simp only [Nf, grNorm]
    congr 1
    ext r
    refine exists_congr fun cf => and_congr_right fun _ => and_congr_right fun _ => and_congr_left fun _ => ?_
    constructor
    · rintro ⟨v, hv, hc⟩
      exact (hP.2 C φ _ v ((comb_comb he' hw' _ ha' cf v).1 hc)).1 hv
    · intro hn
      have hc := (comb_eq hw' cf _).2 rfl
      exact ⟨_, (hP.2 C φ _ _ ((comb_comb he' hw' _ ha' cf _).1 hc)).2 hn, hc⟩
  obtain ⟨-, hprod⟩ := GlobalTheory.LineNorm.Covol.prod_grNorm_eq_iSup_minor ↥C.S g (Fin (M + 1)) (fun j r => ψ (h j r))
    hsep m (fun l r => ψ (a l r)) hli Nf hset
  have hnorm : ∀ k (hk : k ≤ m), ‖fun j => ((φ (F k hk ((Fintype.equivFin _).symm j)) : ↥(intO ↥C.S)) : ↥C.S)‖ =
      ∏ l : Fin k, Nf (Fin.castLE hk l) := by
    intro k hk
    haveI : Nonempty (Fin (Fintype.card (Fin k → Fin (M + 1)))) := ⟨Fintype.equivFin _ (fun _ => 0)⟩
    rw [norm_eq_iSup, hprod k hk]
    refine ((Fintype.equivFin _).symm.iSup_comp (g := fun σ => ‖ψ (F k hk σ)‖)).trans ?_
    congr 1
    funext σ
    simp only [F, map_sum, map_mul, map_prod, map_minor]
  rw [hnorm, hnorm, Fin.prod_univ_castSucc, mul_comm]
  rfl

end GlobalTheory.HTLine.GrMinor

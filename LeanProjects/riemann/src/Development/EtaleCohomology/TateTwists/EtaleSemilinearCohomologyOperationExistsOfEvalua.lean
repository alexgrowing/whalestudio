import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass
import Development.EtaleCohomology.TateTwists.EtaleCochainSemilinearMapOnClasses

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

def LateralTheory.EtaleFoundations.pp_ev_basic : Prop :=
  ∀ (R : Type) [CommRing R] {E : Spc} {I : Cx R} {n : ℤ}, (∀ (α β : Cochain ((chains R).obj E) I n) p s h U x, ev (α + β) p s h U x = ev α p s h U x + ev β p s h U x ∧ ev (α - β) p s h U x = ev α p s h U x - ev β p s h U x ∧ ev (0 : Cochain ((chains R).obj E) I n) p s h U x = 0 ∧ ∀ c : ℤ, ev (c • α) p s h U x = c • ev α p s h U x) ∧ (∀ (α : Cochain ((chains R).obj E) I n) p s h (V U : Scheme.{0}) (g : V ⟶ U) (x : Sx E p U), Sec.res g (ev α p s h U x) = ev α p s h V (x.res g)) ∧ (∀ α β : Cochain ((chains R).obj E) I n, (∀ p s h U x, ev α p s h U x = ev β p s h U x) → α = β) ∧ (∀ {E' : Spc} (f : E' ⟶ E) (α : Cochain ((chains R).obj E) I n) p s h U (x : Sx E' p U), ev ((Cochain.ofHom ((chains R).map f)).comp α (zero_add n)) p s h U x = ev α p s h U (x.map f)) ∧ ∀ {J : Cx R} (m : I ⟶ J) (α : Cochain ((chains R).obj E) I n) p s h U x, ev (α.comp (Cochain.ofHom m) (add_zero n)) p s h U x = Sec.map (m.f s) (ev α p s h U x)

def LateralTheory.EtaleFoundations.pp_ev_mk : Prop :=
  ∀ (R : Type) [CommRing R] {E : Spc} {I : Cx R} {n : ℤ} (a : ∀ (p : ℕ) (s : ℤ), -(p : ℤ) + n = s → ∀ U : Scheme.{0}, Sx E p U → Sec (I.X s) U), (∀ p s h (V U : Scheme.{0}) (g : V ⟶ U) (x : Sx E p U), Sec.res g (a p s h U x) = a p s h V (x.res g)) → ∃ α : Cochain ((chains R).obj E) I n, ∀ p s h U x, ev α p s h U x = a p s h U x

def LateralTheory.EtaleFoundations.pp_ev_delta : Prop :=
  ∀ (R : Type) [CommRing R] {E : Spc} {I : Cx R} {n m : ℤ} (hm : n + 1 = m) (α : Cochain ((chains R).obj E) I n) (U : Scheme.{0}), (∀ (x : Sx E 0 U), ev (δ n m α) 0 m (by simp) U x = Sec.map (I.d n m) (ev α 0 n (by simp) U x)) ∧ ∀ (p : ℕ) (s t : ℤ) (hs : -((p + 1 : ℕ) : ℤ) + n = s) (ht : -((p + 1 : ℕ) : ℤ) + m = t) (x : Sx E (p + 1) U), ev (δ n m α) (p + 1) t ht U x = Sec.map (I.d s t) (ev α (p + 1) s hs U x) + m.negOnePow • ∑ i : Fin (p + 2), (-1 : ℤ) ^ (i : ℕ) • ev α p t (by omega) U (x.face i)

namespace LateralTheory.EtaleFoundations.OpPf
variable {S R : Type} [CommRing S] [CommRing R] {I : Cx S} {J : Cx R}

theorem img_ex (hB : LateralTheory.EtaleFoundations.pp_ev_basic) (hM : LateralTheory.EtaleFoundations.pp_ev_mk) (ρ : SemiMap I J) {E : Spc} {n : ℤ}
    (α : Cochain ((chains S).obj E) I n) : ∃ β, ρ.IsImage α β := by
  obtain ⟨β, hβ⟩ := hM R (E := E) (I := J) (n := n) (fun p s h U x => ρ.app U s (ev α p s h U x)) (by
    intro p s h V U g x
    rw [ρ.nat, (hB S).2.1])
  exact ⟨β, fun p s h U x => hβ p s h U x⟩

theorem img_unique (hB : LateralTheory.EtaleFoundations.pp_ev_basic) (ρ : SemiMap I J) {E : Spc} {n : ℤ}
    {α : Cochain ((chains S).obj E) I n} {β β' : Cochain ((chains R).obj E) J n}
    (h : ρ.IsImage α β) (h' : ρ.IsImage α β') : β = β' :=
  (hB R).2.2.1 β β' (fun p s hh U x => by rw [h, h'])

theorem img_delta (hD : LateralTheory.EtaleFoundations.pp_ev_delta) (ρ : SemiMap I J) {E : Spc} {n m : ℤ} (hm : n + 1 = m)
    {α : Cochain ((chains S).obj E) I n} {β : Cochain ((chains R).obj E) J n}
    (h : ρ.IsImage α β) : ρ.IsImage (δ n m α) (δ n m β) := by
  intro p t ht U x
  cases p with
  | zero =>
    obtain rfl : t = m := by omega
    rw [(hD R hm β U).1 x, (hD S hm α U).1 x, h, ρ.comm]
  | succ p =>
    rw [(hD R hm β U).2 p _ t rfl ht x, (hD S hm α U).2 p _ t rfl ht x]
    rw [map_add, ← ρ.comm, ← h]
    congr 1
    rw [Units.smul_def, Units.smul_def, map_zsmul, map_sum]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_zsmul, ← h]

theorem img_cocycle (hB : LateralTheory.EtaleFoundations.pp_ev_basic) (hM : LateralTheory.EtaleFoundations.pp_ev_mk) (hD : LateralTheory.EtaleFoundations.pp_ev_delta)
    (ρ : SemiMap I J) {E : Spc} {n : ℤ} (α : Cocycle ((chains S).obj E) I n) :
    ∃ β : Cocycle ((chains R).obj E) J n, ρ.IsImage α.1 β.1 := by
  obtain ⟨β, hβ⟩ := img_ex hB hM ρ α.1
  refine ⟨Cocycle.mk β (n + 1) rfl ?_, hβ⟩
  have h1 := img_delta hD ρ rfl hβ
  rw [Cocycle.δ_eq_zero] at h1
  have h0 : ρ.IsImage (0 : Cochain ((chains S).obj E) I (n + 1)) (0 : Cochain ((chains R).obj E) J (n + 1)) := by
    intro p s h U x
    rw [((hB R).1 0 0 p s h U x).2.2.1, ((hB S).1 0 0 p s h U x).2.2.1, map_zero]
  exact img_unique hB ρ h1 h0

noncomputable def img (hB : LateralTheory.EtaleFoundations.pp_ev_basic) (hM : LateralTheory.EtaleFoundations.pp_ev_mk) (hD : LateralTheory.EtaleFoundations.pp_ev_delta)
    (ρ : SemiMap I J) {E : Spc} {n : ℤ} (α : Cocycle ((chains S).obj E) I n) : Cocycle ((chains R).obj E) J n :=
  (img_cocycle hB hM hD ρ α).choose

theorem img_spec (hB : LateralTheory.EtaleFoundations.pp_ev_basic) (hM : LateralTheory.EtaleFoundations.pp_ev_mk) (hD : LateralTheory.EtaleFoundations.pp_ev_delta)
    (ρ : SemiMap I J) {E : Spc} {n : ℤ} (α : Cocycle ((chains S).obj E) I n) : ρ.IsImage α.1 (img hB hM hD ρ α).1 :=
  (img_cocycle hB hM hD ρ α).choose_spec

theorem img_eq (hB : LateralTheory.EtaleFoundations.pp_ev_basic) (hM : LateralTheory.EtaleFoundations.pp_ev_mk) (hD : LateralTheory.EtaleFoundations.pp_ev_delta)
    (ρ : SemiMap I J) {E : Spc} {n : ℤ} (α : Cocycle ((chains S).obj E) I n) (β : Cocycle ((chains R).obj E) J n)
    (h : ρ.IsImage α.1 β.1) : img hB hM hD ρ α = β :=
  Cocycle.ext (img_unique hB ρ (img_spec hB hM hD ρ α) h)

noncomputable def zmap (hB : LateralTheory.EtaleFoundations.pp_ev_basic) (hM : LateralTheory.EtaleFoundations.pp_ev_mk) (hD : LateralTheory.EtaleFoundations.pp_ev_delta)
    (ρ : SemiMap I J) (E : Spc) (n : ℤ) : Cocycle ((chains S).obj E) I n →+ CohomologyClass ((chains R).obj E) J n :=
  AddMonoidHom.mk' (fun α => CohomologyClass.mk (img hB hM hD ρ α)) (fun a b => by
    rw [← CohomologyClass.mk_add]
    congr 1
    apply img_eq
    intro p s h U x
    have ha := img_spec hB hM hD ρ a p s h U x
    have hb := img_spec hB hM hD ρ b p s h U x
    change ev ((img hB hM hD ρ a).1 + (img hB hM hD ρ b).1) p s h U x = ρ.app U s (ev (a.1 + b.1) p s h U x)
    rw [((hB R).1 _ _ p s h U x).1, ((hB S).1 _ _ p s h U x).1, map_add, ha, hb])

noncomputable def theOp (hB : LateralTheory.EtaleFoundations.pp_ev_basic) (hM : LateralTheory.EtaleFoundations.pp_ev_mk) (hD : LateralTheory.EtaleFoundations.pp_ev_delta)
    (ρ : SemiMap I J) : NatOp I J where
  app E n := CohomologyClass.descAddMonoidHom (zmap hB hM hD ρ E n) (by
    intro α hα
    obtain ⟨γ, hγ⟩ := (mem_coboundaries_iff α (n - 1) (by omega)).1 hα
    obtain ⟨γ', hγ'⟩ := img_ex hB hM ρ γ
    have h1 := img_delta hD ρ (by omega : n - 1 + 1 = n) hγ'
    rw [hγ] at h1
    have h2 := img_eq hB hM hD ρ α (Cocycle.mk (δ (n - 1) n γ') (n + 1) rfl (δ_δ _ _ _ _)) h1
    change CohomologyClass.mk (img hB hM hD ρ α) = 0
    rw [h2, CohomologyClass.mk_eq_zero_iff, mem_coboundaries_iff _ (n - 1) (by omega)]
    exact ⟨γ', rfl⟩)
  nat := by
    intro E E' f n x
    obtain ⟨α, rfl⟩ := CohomologyClass.mk_surjective x
    change CohomologyClass.mk (zcomp _ (img hB hM hD ρ α) (zero_add n)) =
      CohomologyClass.mk (img hB hM hD ρ (zcomp _ α (zero_add n)))
    congr 1
    symm
    apply img_eq
    intro p s h U y
    change ev ((Cochain.ofHom ((chains R).map f)).comp (img hB hM hD ρ α).1 (zero_add n)) p s h U y =
      ρ.app U s (ev ((Cochain.ofHom ((chains S).map f)).comp α.1 (zero_add n)) p s h U y)
    rw [(hB R).2.2.2.1, (hB S).2.2.2.1, img_spec hB hM hD ρ α]

end LateralTheory.EtaleFoundations.OpPf

open LateralTheory.EtaleFoundations.OpPf in
theorem LateralTheory.EtaleFoundations.etale_semilinear_cohomology_operation_exists_of_evaluation (hB : LateralTheory.EtaleFoundations.pp_ev_basic) (hM : LateralTheory.EtaleFoundations.pp_ev_mk)
    (hD : LateralTheory.EtaleFoundations.pp_ev_delta) : LateralTheory.EtaleFoundations.EtaleCochainSemilinearMapOnClasses := by
  intro S R _ _ I J ρ
  refine ⟨fun E n α => img_cocycle hB hM hD ρ α, fun E n α β h => ?_⟩
  have hc : ∃ c : NatOp I J, ∀ (E : Spc) (n : ℤ) (α : Cocycle ((chains S).obj E) I n) (β : Cocycle ((chains R).obj E) J n),
      (∀ (p : ℕ) (s : ℤ) (h : -(p : ℤ) + n = s) (U : Scheme.{0}) (x : Sx E p U), ev β.1 p s h U x = ρ.app U s (ev α.1 p s h U x)) →
      c.app E n (CohomologyClass.mk α) = CohomologyClass.mk β := by
    refine ⟨theOp hB hM hD ρ, fun E n α β h => ?_⟩
    change CohomologyClass.mk (img hB hM hD ρ α) = CohomologyClass.mk β
    rw [img_eq hB hM hD ρ α β h]
  exact pick_spec hc E n α β h

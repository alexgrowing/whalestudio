import Development.AutomorphicSpectrum.Statements.GeometryStatements.IsPolLatticePlane
import Development.WeilBound.CoreStatements.HodgeTatePoints.TwpdivHopf
import Development.WeilBound.CoreStatements.HodgeTatePoints.TwpdivTate

noncomputable section

namespace PositivityTheory.HtPt.Twpdiv

open TensorProduct GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup WithConv GlobalTheory.CompanionTheory.Ar.BT GlobalTheory.CompanionTheory.Ar.HT Coalgebra Bialgebra

section Lev

variable {La : Type} [AddCommGroup La] (p : ℕ)

theorem lev_surjective (n : ℕ) : Function.Surjective (lev (La := La) p n) := fun t =>
  Submodule.Quotient.mk_surjective _ (Multiplicative.toAdd t)

theorem lev_eq_iff (n : ℕ) (a a' : La) : lev p n a = lev p n a' ↔ ∃ b : La, a - a' = (p ^ n) • b := by
  rw [lev, lev, Multiplicative.ofAdd.apply_eq_iff_eq, Submodule.Quotient.eq]
  exact ⟨fun ⟨b, hb⟩ => ⟨b, hb.symm⟩, fun ⟨b, hb⟩ => ⟨b, hb.symm⟩⟩

theorem lev_add (n : ℕ) (a a' : La) : lev p n (a + a') = lev p n a * lev p n a' := rfl

theorem lev_zero (n : ℕ) : lev p n (0 : La) = 1 := rfl

theorem lev_nsmul (n k : ℕ) (a : La) : lev p n (k • a) = lev p n a ^ k := by
  induction k with
  | zero => simp [lev_zero]
  | succ k ih => rw [succ_nsmul, lev_add, ih, pow_succ]

theorem lev_pow (n : ℕ) (t : LevGrp La p n) : t ^ p ^ n = 1 := by
  obtain ⟨a, rfl⟩ := lev_surjective p n t
  rw [← lev_nsmul, ← lev_zero, lev_eq_iff]
  exact ⟨a, sub_zero _⟩

def incl (n : ℕ) : LevGrp La p n →* LevGrp La p (n + 1) :=
  AddMonoidHom.toMultiplicative (Submodule.mapQ _ _ (p • (LinearMap.id : La →ₗ[ℤ] La)) (by
    rintro _ ⟨b, rfl⟩
    exact ⟨b, by simp only [LinearMap.smul_apply, LinearMap.id_apply, pow_succ', mul_smul]⟩)).toAddMonoidHom

theorem incl_lev (n : ℕ) (a : La) : incl p n (lev p n a) = lev p (n + 1) (p • a) := rfl

theorem card_lev [Module.Free ℤ La] [Module.Finite ℤ La] (n : ℕ) :
    Nat.card (LevGrp La p n) = p ^ (n * Module.finrank ℤ La) := by
  rw [pow_mul, ← AddSubgroup.index_range_nsmul]
  have : (nsmulAddMonoidHom (α := La) (p ^ n)).range =
      (LinearMap.range ((p ^ n) • (LinearMap.id : La →ₗ[ℤ] La))).toAddSubgroup := by
    ext x; exact Iff.rfl
  rw [this]
  rfl

instance [Fact p.Prime] [Module.Free ℤ La] [Module.Finite ℤ La] (n : ℕ) : Finite (LevGrp La p n) :=
  Nat.finite_of_card_ne_zero (by rw [card_lev]; exact pow_ne_zero _ (Fact.out : p.Prime).ne_zero)

end Lev

variable {p : ℕ} [Fact p.Prime] {O : Type} [CommRing O] {La : Type} [AddCommGroup La] [Module.Free ℤ La]
  [Module.Finite ℤ La] {L : Type} [AddCommGroup L] [Module O L] (X : OrdTower p O La L)

def resT (n : ℕ) : Ord (X.hopf (n + 1)) →ₐc[O] Ord (X.hopf n) :=
  Ord.comap (X.hopf n) (X.hopf (n + 1)) (incl p n) fun f hf => (X.res_iff n _).2 ⟨f, hf, fun _ => rfl⟩

theorem ev_resT (n : ℕ) (t : LevGrp La p n) (f : Ord (X.hopf (n + 1))) :
    Ord.ev _ t (resT X n f) = Ord.ev _ (incl p n t) f := Ord.ev_comap _ _ _ _ t f

theorem resT_surjective (n : ℕ) : Function.Surjective (resT X n) := fun g => by
  obtain ⟨f, hf, h⟩ := (X.res_iff n _).1 (Ord.equiv _ g).2
  refine ⟨(Ord.equiv _).symm ⟨f, hf⟩, Ord.sep _ _ _ fun t => ?_⟩
  obtain ⟨a, rfl⟩ := lev_surjective p n t
  rw [ev_resT]
  exact (h a).symm

theorem ker_resT (n : ℕ) : RingHom.ker (resT X n) = torsionIdeal O (Ord (X.hopf (n + 1))) (p ^ n) := by
  apply le_antisymm
  · intro f hf
    have hf' : resT X n f = 0 := hf
    have h1 := X.ker_res n (Ord.equiv _ f) fun a => by
      have := ev_resT X n (lev p n a) f
      rw [hf', map_zero] at this
      exact this.symm
    have h2 : Ideal.span {g : X.A (n + 1) | ∃ h ∈ X.A (n + 1), ∀ t, g.1 t = h (t ^ p ^ n) - h 1} ≤
        (torsionIdeal O (Ord (X.hopf (n + 1))) (p ^ n)).comap (Ord.equiv (X.hopf (n + 1))).symm := by
      rw [Ideal.span_le]
      rintro g ⟨u, hu, hg⟩
      let u' := (Ord.equiv (X.hopf (n + 1))).symm ⟨u, hu⟩
      have h3 : (Ord.equiv (X.hopf (n + 1))).symm g =
          mulBy O _ (p ^ n) (u' - algebraMap O _ (counit u')) := Ord.sep _ _ _ fun t => by
        rw [Ord.ev_mulBy, map_sub, AlgHom.commutes, Ord.counit_eq]
        exact hg t
      change (Ord.equiv (X.hopf (n + 1))).symm g ∈ torsionIdeal O (Ord (X.hopf (n + 1))) (p ^ n)
      rw [h3]
      exact Ideal.mem_map_of_mem _ (by simp [RingHom.mem_ker])
    exact h2 h1
  · refine (kerIdeal_le_ker_iff _ (resT X n : Ord (X.hopf (n + 1)) →ₐ[O] Ord (X.hopf n))).2 fun c =>
      Ord.sep _ _ _ fun t => ?_
    rw [AlgHom.commutes]
    change Ord.ev _ t (resT X n _) = _
    rw [ev_resT, Ord.ev_mulBy, ← map_pow, lev_pow, map_one, Ord.counit_eq]
    rfl

variable [IsDomain O] [IsLocalRing O]

def grp : PDivGroup p O where
  height := Module.finrank ℤ La
  A n := Ord (X.hopf n)
  rank_eq n q := by rw [Ord.rankAtStalk_eq, card_lev]
  res := resT X
  res_surjective := resT_surjective X
  ker_res := ker_resT X

def tau : La →+ (grp X).Tate :=
  AddMonoidHom.mk' (fun a => ⟨fun n => Ord.ev (X.hopf n) (lev p n a), fun n => AlgHom.ext fun g => by
      obtain ⟨f, rfl⟩ := (grp X).res_surjective n g
      refine (congrArg (Ord.ev (X.hopf (n + 1)) (lev p (n + 1) a)) ((grp X).mulP_res n f)).trans ?_
      refine (Ord.ev_mulBy _ _ p f).trans ?_
      rw [← lev_nsmul]
      exact (ev_resT X n (lev p n a) f).symm⟩)
    fun a b => TateOver.ext_conv fun n => map_mul (Ord.evHom (X.hopf n)) (lev p n a) (lev p n b)

theorem realises : X.Realises (grp X) (fun n => Ord.equiv (X.hopf n)) (tau X) :=
  ⟨fun n f a => ev_resT X n (lev p n a) f, fun _ _ _ => rfl⟩

theorem exists_tate : ∃ j : ℤ_[p] ⊗[ℤ] La ≃ₗ[ℤ_[p]] (grp X).Tate, ∀ a, j (1 ⊗ₜ a) = tau X a :=
  tate_equiv (tau X)
    (fun n a a' => ((Ord.evHom_bijective (X.hopf n)).1.eq_iff (a := lev p n a) (b := lev p n a')).trans
      (lev_eq_iff p n a a'))
    fun n y => by
      obtain ⟨t, ht⟩ := (Ord.evHom_bijective (X.hopf n)).2 y
      obtain ⟨a, rfl⟩ := lev_surjective p n t
      exact ⟨a, ht⟩

end PositivityTheory.HtPt.Twpdiv

end

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct NumberField GlobalTheory GlobalTheory.PDivGroup GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.BT GlobalTheory.CompanionTheory.Ar.HT ReciprocityTheory.ChartRestriction.G.Semi

theorem PositivityTheory.HtPt.Twpdiv.tower_pdiv : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [IsDomain O] [Algebra O C] (hv : v.Integers O) (hp : v (p : C) < 1) (hO : IsAdicComplete (Ideal.span {(p : O)}) O) (La : Type) [AddCommGroup La] [Module.Free ℤ La] [Module.Finite ℤ La] (L : Type) [AddCommGroup L] [Module O L] (X : OrdTower p O La L), ∃ (G : PDivGroup p O) (e : ∀ n, G.A n ≃ₐ[O] X.A n) (τ : La →+ G.Tate), X.Realises G e τ ∧ G.height = Module.finrank ℤ La ∧ ∃ j : ℤ_[p] ⊗[ℤ] La ≃ₗ[ℤ_[p]] G.Tate, ∀ a, j (1 ⊗ₜ a) = τ a := by
  intro p _ C _ _ _ v O _ _ _ hv _ _ La _ _ _ L _ _ X
  have : ValuationRing O := ValuationRing.of_integers v hv
  exact ⟨PositivityTheory.HtPt.Twpdiv.grp X, _, _, PositivityTheory.HtPt.Twpdiv.realises X, rfl, PositivityTheory.HtPt.Twpdiv.exists_tate X⟩

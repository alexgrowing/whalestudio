import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsQuasiInv
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsClopenTorsionKernelLocus
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsFiniteEtaleLatticeTorsionHom

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES

namespace UpperTheory.TjLocus

open GlobalTheory.LevCover GlobalTheory.LatticeTorsion

private theorem exists_stable_exponent {S : Type} [CommRing S] (I u : Ideal S) [Finite (S ⧸ I)] :
    ∃ E : ℕ, ∀ J : Ideal S, I ≤ J → ∀ n : ℕ, u ^ n ≤ J → u ^ E ≤ J := by
  classical
  let f : ℕ →o (Ideal (S ⧸ I))ᵒᵈ :=
    ⟨fun n => OrderDual.toDual (Ideal.map (Ideal.Quotient.mk I) (u ^ n)), fun m n hmn =>
      Ideal.map_mono (Ideal.pow_le_pow_right hmn)⟩
  obtain ⟨E, hE⟩ := IsArtinian.monotone_stabilizes f
  refine ⟨E, fun J hIJ n hn => ?_⟩
  rcases le_total n E with h | h
  · exact (Ideal.pow_le_pow_right h).trans hn
  · have hfe : Ideal.map (Ideal.Quotient.mk I) (u ^ E) = Ideal.map (Ideal.Quotient.mk I) (u ^ n) := hE n h
    calc u ^ E ≤ Ideal.comap (Ideal.Quotient.mk I) (Ideal.map (Ideal.Quotient.mk I) (u ^ E)) :=
          Ideal.le_comap_map
      _ = Ideal.comap (Ideal.Quotient.mk I) (Ideal.map (Ideal.Quotient.mk I) (u ^ n)) := by rw [hfe]
      _ ≤ Ideal.comap (Ideal.Quotient.mk I) (Ideal.map (Ideal.Quotient.mk I) J) :=
          Ideal.comap_mono (Ideal.map_mono hn)
      _ = J := Ideal.comap_map_mk hIJ

private theorem charZero_of_point {R : Type} [CommRing R] (hu : ∀ n : ℕ, n ≠ 0 → IsUnit (n : R)) {k : Type} [Field k]
    (y : Sp k ⟶ Sp R) : CharZero k := by
  refine charZero_of_inj_zero fun n hn => ?_
  by_contra h0
  have h := (hu n h0).map (Spec.preimage y).hom
  rw [map_natCast, hn] at h
  exact not_isUnit_zero h

variable {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R] {b : Base D R} {N : ℕ} {Y : Scheme.{0}}
  {s : Y ⟶ Sp R}

private theorem act_zero (o : Obj b N s) : o.act.act (0 : D.O) = 1 := by
  have h := o.act.add 0 0
  rw [add_zero] at h
  exact left_eq_mul.mp h

private theorem comp_act_natCast (o : Obj b N s) {T : Over Y} (g : T ⟶ o.A) (n : ℕ) :
    g ≫ o.act.act (n : D.O) = g ^ n := by
  induction n with
  | zero => rw [Nat.cast_zero, act_zero, MonObj.comp_one, pow_zero]
  | succ n ih =>
    rw [Nat.cast_succ, o.act.add, MonObj.comp_mul, ih, o.act.one, Category.comp_id, pow_succ]

private def ann (o : Obj b N s) {T : Over Y} (g : T ⟶ o.A) : Ideal (𝓞 D.F) where
  carrier := {a | g ≫ o.act.act (algebraMap (𝓞 D.F) D.O a) = 1}
  add_mem' := by
    intro a a' ha ha'
    simp only [Set.mem_setOf_eq] at ha ha' ⊢
    rw [map_add, o.act.add, MonObj.comp_mul, ha, ha', _root_.one_mul]
  zero_mem' := by
    simp only [Set.mem_setOf_eq]
    rw [map_zero, act_zero, MonObj.comp_one]
  smul_mem' := by
    intro x a ha
    simp only [Set.mem_setOf_eq] at ha ⊢
    haveI := o.act.hom (algebraMap (𝓞 D.F) D.O x)
    rw [smul_eq_mul, map_mul, o.act.mul, ← Category.assoc, ha, MonObj.one_comp]

private theorem killedBy_iff (o : Obj b N s) (v : Ideal (𝓞 D.F)) {T : Over Y} (g : T ⟶ o.A) :
    KilledBy o v g ↔ v ≤ ann o g := Iff.rfl

private theorem clopen_killedBy (o : Obj b N s) (c : ℕ) (hc : IsUnit (c : Γ(Y, ⊤))) (I : Ideal (𝓞 D.F)) :
    ClopenCond (torsion o.A c) fun _ z => KilledBy o I (z ≫ torsion.ι o.A c) := by
  haveI := o.ab
  obtain ⟨t, ht⟩ := (IsNoetherian.noetherian I : I.FG)
  have hgen : ∀ a : (t : Set (𝓞 D.F)), ClopenCond (torsion o.A c) fun _ z =>
      z ≫ (torsion.ι o.A c ≫ o.act.act (algebraMap (𝓞 D.F) D.O a)) = 1 := by
    intro a
    haveI := o.act.hom (algebraMap (𝓞 D.F) D.O a)
    refine clopenCond_comp_eq_one _ o.A o.ab c hc _ ?_
    rw [← MonObj.pow_comp, torsionι_pow_eq_one, MonObj.one_comp]
  refine (ClopenCond.forall_finite hgen).congr fun T' z => ?_
  rw [killedBy_iff, ← ht, Submodule.span_le]
  constructor
  · intro h a
    have := h a.2
    change (z ≫ torsion.ι o.A c) ≫ _ = 1 at this
    simpa only [Category.assoc] using this
  · intro h a ha
    change (z ≫ torsion.ι o.A c) ≫ _ = 1
    simpa only [Category.assoc] using h ⟨a, ha⟩

private theorem card_points {V A : Over Y} [IsFinite V.hom] [Etale V.hom] (j : V ⟶ A)
    (hj : ∀ {T : Over Y} (a a' : T ⟶ V), a ≫ j = a' ≫ j → a = a') (C : ∀ T : Over Y, (T ⟶ A) → Prop)
    (h1 : ∀ {T : Over Y} (h' : T ⟶ V), C T (h' ≫ j)) (h2 : ∀ {T : Over Y} (g : T ⟶ A), C T g → ∃ h' : T ⟶ V, h' ≫ j = g)
    {k : Type} [Field k] [IsAlgClosed k] (x : Sp k ⟶ Y) (q : Sp k) :
    V.hom.finrank (x q) = Nat.card {g : Over.mk x ⟶ A // C _ g} := by
  obtain ⟨-, hcard⟩ := GlobalTheory.FinEt.card_points_eq_finrank V.hom x q
  rw [← hcard]
  refine Nat.card_eq_of_bijective (fun v => ⟨Over.homMk v.1 v.2 ≫ j, h1 _⟩) ⟨?_, ?_⟩
  · intro v v' hvv
    have h := hj _ _ (congrArg Subtype.val hvv)
    exact Subtype.ext (congrArg (fun m => m.left) h)
  · rintro ⟨g, hg⟩
    obtain ⟨h', hh'⟩ := h2 g hg
    refine ⟨⟨h'.left, Over.w h'⟩, Subtype.ext ?_⟩
    change Over.homMk h'.left _ ≫ j = g
    rw [← hh']
    congr 1

private theorem exists_count_scheme (o : Obj b N s) {B : Over Y} [GrpObj B] (hB : IsAbelianScheme B) (ψ : o.A ⟶ B)
    [IsMonHom ψ] (c : ℕ) (hc : IsUnit (c : Γ(Y, ⊤))) (hkill : ∀ {T : Over Y} (g : T ⟶ o.A), g ≫ ψ = 1 → g ^ c = 1)
    (w : Ideal (𝓞 D.F)) :
    ∃ V : Over Y, IsFinite V.hom ∧ Etale V.hom ∧ ∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ Y) (q : Sp k),
      V.hom.finrank (x q) = Nat.card {g : Over.mk x ⟶ o.A // g ≫ ψ = 1 ∧ KilledBy o w g} := by
  haveI := o.ab
  obtain ⟨-, hTf, hTe⟩ := GlobalTheory.GrpTangent.finiteEtale_mulN_torsion o.A hc
  have hψc : (torsion.ι o.A c ≫ ψ) ^ c = 1 := by
    rw [← MonObj.pow_comp, torsionι_pow_eq_one, MonObj.one_comp]
  have hP : ClopenCond (torsion o.A c) fun _ z =>
      z ≫ (torsion.ι o.A c ≫ ψ) = 1 ∧ KilledBy o w (z ≫ torsion.ι o.A c) :=
    (clopenCond_comp_eq_one _ B hB c hc _ hψc).and (clopen_killedBy o c hc w)
  obtain ⟨U, hU, hUiff⟩ := hP
  haveI := hTf
  haveI := hTe
  obtain ⟨V, i, hVf, hVe, hi, hVi⟩ := exists_sub U hU
  haveI := hVf
  haveI := hVe
  refine ⟨V, hVf, hVe, fun k _ _ x q => ?_⟩
  have hιinj : ∀ {T : Over Y} (a a' : T ⟶ torsion o.A c),
      a ≫ torsion.ι o.A c = a' ≫ torsion.ι o.A c → a = a' := by
    intro T a a' h
    have hpow : (a ≫ torsion.ι o.A c) ^ c = 1 := by
      rw [← MonObj.comp_pow, torsionι_pow_eq_one, MonObj.comp_one]
    exact (existsUnique_torsion o.A c _ hpow).unique rfl h.symm
  refine card_points (i ≫ torsion.ι o.A c) ?_ (fun T g => g ≫ ψ = 1 ∧ KilledBy o w g) ?_ ?_ x q
  · intro T a a' h
    exact (cancel_mono i).mp (hιinj _ _ (by simpa only [Category.assoc] using h))
  · intro T h'
    have := (hUiff T (h' ≫ i)).mpr ((hVi T (h' ≫ i)).mpr ⟨h', rfl⟩)
    simpa only [Category.assoc] using this
  · intro T g hg
    obtain ⟨y, hy, -⟩ := existsUnique_torsion o.A c g (hkill g hg.1)
    have hPy : y ≫ (torsion.ι o.A c ≫ ψ) = 1 ∧ KilledBy o w (y ≫ torsion.ι o.A c) := by
      rw [← Category.assoc, hy]
      exact hg
    obtain ⟨h', hh'⟩ := (hVi T y).mp ((hUiff T y).mp hPy)
    exact ⟨h', by rw [← Category.assoc, hh', hy]⟩

private theorem exists_killed_locus (o : Obj b N s) {B : Over Y} [GrpObj B] (hB : IsAbelianScheme B) (ψ : o.A ⟶ B)
    [IsMonHom ψ] (c : ℕ) (hc0 : c ≠ 0) (hc : IsUnit (c : Γ(Y, ⊤)))
    (hkill : ∀ {T : Over Y} (g : T ⟶ o.A), g ≫ ψ = 1 → g ^ c = 1) (r : ℤ) (w : Ideal (𝓞 D.F)) :
    ∃ W : Set Y, IsOpen W ∧ IsClosed W ∧ ∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ Y),
      Set.range x.base ⊆ W ↔
      ∀ g : Over.mk x ⟶ o.A, g ≫ ψ = 1 → (∃ e : ℕ, KilledBy o (uIdeal D r ^ e) g) → KilledBy o w g := by
  haveI := o.ab
  obtain ⟨-, hTf, hTe⟩ := GlobalTheory.GrpTangent.finiteEtale_mulN_torsion o.A hc
  haveI : Finite (𝓞 D.F ⧸ Ideal.span {(c : 𝓞 D.F)}) :=
    Ideal.finiteQuotientOfFreeOfNeBot _ (by
      rw [Ne, Ideal.span_singleton_eq_bot]
      exact_mod_cast hc0)
  obtain ⟨E, hE⟩ := exists_stable_exponent (Ideal.span {(c : 𝓞 D.F)}) (uIdeal D r)
  have hcann : ∀ {T : Over Y} (z : T ⟶ torsion o.A c),
      Ideal.span {(c : 𝓞 D.F)} ≤ ann o (z ≫ torsion.ι o.A c) := by
    intro T z
    rw [Ideal.span_le, Set.singleton_subset_iff]
    change (z ≫ torsion.ι o.A c) ≫ o.act.act (algebraMap (𝓞 D.F) D.O (c : 𝓞 D.F)) = 1
    rw [map_natCast, comp_act_natCast, ← MonObj.comp_pow, torsionι_pow_eq_one, MonObj.comp_one]
  have hex : ∀ {T : Over Y} (z : T ⟶ torsion o.A c),
      (∃ e : ℕ, KilledBy o (uIdeal D r ^ e) (z ≫ torsion.ι o.A c)) ↔
        KilledBy o (uIdeal D r ^ E) (z ≫ torsion.ι o.A c) := by
    intro T z
    simp only [killedBy_iff]
    exact ⟨fun ⟨e, he⟩ => hE _ (hcann z) e he, fun h => ⟨E, h⟩⟩
  have hψc : (torsion.ι o.A c ≫ ψ) ^ c = 1 := by
    rw [← MonObj.pow_comp, torsionι_pow_eq_one, MonObj.one_comp]
  have hP : ClopenCond (torsion o.A c) fun _ z =>
      z ≫ (torsion.ι o.A c ≫ ψ) = 1 ∧ ∃ e : ℕ, KilledBy o (uIdeal D r ^ e) (z ≫ torsion.ι o.A c) :=
    ((clopenCond_comp_eq_one _ B hB c hc _ hψc).and (clopen_killedBy o c hc _)).congr
      fun _ z => and_congr_right' (hex z)
  obtain ⟨W, hWo, hWc, -, hW⟩ :=
    implocus_open_closed Y (torsion o.A c) _ _ hTf hTe hP (clopen_killedBy o c hc w)
  refine ⟨W, hWo, hWc, fun k _ _ x => (hW k x).trans ⟨fun h g hg he => ?_, fun h z hz => ?_⟩⟩
  · obtain ⟨y, hy, -⟩ := existsUnique_torsion o.A c g (hkill g hg)
    subst hy
    exact h y ⟨by simpa only [Category.assoc] using hg, he⟩
  · exact h _ (by simpa only [Category.assoc] using hz.1) hz.2

end UpperTheory.TjLocus

theorem UpperTheory.Cb.exists_clopen_locus_of_annihilator :
    ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ) (c : ℕ) (Y : Scheme.{0}) (s : Y ⟶ Sp R) (o : Obj b N s) (B : Over Y) [GrpObj B] [IsCommMonObj B] (ψ : o.A ⟶ B) (ψ' : B ⟶ o.A), IsUnit ((p : ℕ) : R) → (∃ e : ℕ, c = p ^ e) → IsAbelianScheme B → IsQuasiInv c ψ ψ' → ∀ (r : ℤ) (w : Ideal (𝓞 D.F)) (j : ℕ), ∃ W : Set Y, IsOpen W ∧ IsClosed W ∧ ∀ (Tb : Scheme.{0}) (t : Tb ⟶ Y), Set.range t.base ⊆ W ↔ TjAt r w j o ψ t := by
  intro p _ D R _ b N c Y s o B _ _ ψ ψ' hp hce hB hq r w j
  obtain ⟨e, hce⟩ := hce
  obtain ⟨hψ, hψ', hψψ', -⟩ := hq
  haveI := hψ
  haveI := hψ'
  have hpp : p.Prime := Fact.out
  have hu : ∀ n : ℕ, n ≠ 0 → IsUnit (n : R) := by
    intro n hn
    obtain ⟨a, m, hm, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hn p hpp.one_lt.ne'
    rw [Nat.cast_mul, Nat.cast_pow]
    exact (hp.pow a).mul (b.unit m (Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd hpp).mpr hm)))
  have hc0 : c ≠ 0 := by
    rw [hce]
    exact pow_ne_zero _ hpp.ne_zero
  have hc : IsUnit (c : Γ(Y, ⊤)) := by
    have := (hu c hc0).map ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ s.appTop).hom
    rwa [map_natCast] at this
  have hkill : ∀ {T : Over Y} (g : T ⟶ o.A), g ≫ ψ = 1 → g ^ c = 1 := by
    intro T g hg
    calc g ^ c = g ≫ (𝟙 o.A ^ c) := by rw [MonObj.comp_pow, Category.comp_id]
      _ = (g ≫ ψ) ≫ ψ' := by rw [← hψψ', Category.assoc]
      _ = 1 := by rw [hg, MonObj.one_comp]
  obtain ⟨W1, hW1o, hW1c, hW1⟩ := UpperTheory.TjLocus.exists_killed_locus o hB ψ c hc0 hc hkill r w
  obtain ⟨V, hVf, hVe, hV⟩ := UpperTheory.TjLocus.exists_count_scheme o hB ψ c hc hkill w
  haveI := hVf
  haveI := hVe
  have hloc := (Scheme.Hom.isLocallyConstant_finrank V.hom).isClopen_fiber (Ideal.absNorm w ^ (D.m * j))
  refine ⟨W1 ∩ {y | V.hom.finrank y = Ideal.absNorm w ^ (D.m * j)}, hW1o.inter hloc.isOpen,
    hW1c.inter hloc.isClosed, fun Tb t => ⟨?_, ?_⟩⟩
  · intro ht k _ _ _ x hσ
    obtain ⟨σ, hσ⟩ := hσ
    have hx : Set.range x.base ⊆ W1 ∩ {y | V.hom.finrank y = Ideal.absNorm w ^ (D.m * j)} := by
      rintro _ ⟨z, rfl⟩
      exact ht ⟨σ.base z, by rw [← hσ]; rfl⟩
    refine ⟨(hW1 k x).mp fun y hy => (hx hy).1, ?_⟩
    obtain ⟨q⟩ : Nonempty (Sp k) := inferInstance
    rw [← hV k x q]
    exact (hx ⟨q, rfl⟩).2
  · intro ht
    rintro _ ⟨z, rfl⟩
    obtain ⟨k, _, _, a, ha⟩ := GlobalTheory.FinEt.exists_algClosed_point Tb z
    haveI : CharZero k := UpperTheory.TjLocus.charZero_of_point hu (a ≫ t ≫ s)
    obtain ⟨hkil, hcnt⟩ := ht k (a ≫ t) ⟨a, rfl⟩
    obtain ⟨q, hq⟩ : z ∈ Set.range a.base := by
      rw [ha]
      exact Set.mem_singleton z
    have hz : (a ≫ t).base q = t.base z := by
      show t.base (a.base q) = _
      rw [hq]
    refine ⟨(hW1 k (a ≫ t)).mpr hkil ⟨q, hz⟩, ?_⟩
    show V.hom.finrank (t.base z) = _
    rw [← hz, hV k (a ≫ t) q]
    exact hcnt

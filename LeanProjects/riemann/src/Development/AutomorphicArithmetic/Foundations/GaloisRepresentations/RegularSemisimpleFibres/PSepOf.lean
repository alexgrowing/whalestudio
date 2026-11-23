import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.SuppBCOfMix
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.ResEmbCompat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NotModEqOfLt

open NumberField IsDedekindDomain ValuativeRel Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.L2.Host
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Shin
open GroundTheory.Global GroundTheory.Global.SemiLocal UpperTheory.V.Published UpperTheory.CBC UpperTheory.Gal.InertialTypesAlt
open scoped Classical
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.Gal.InertialTypesAlt.SeparatedBlocks

private theorem key {N M c x y : ℕ} (hc0 : 0 < c) (h : M * c = N) :
    ((x * c : ℕ) : ZMod N) = ((y * c : ℕ) : ZMod N) ↔ x ≡ y [MOD M] := by
  subst h
  rw [ZMod.natCast_eq_natCast_iff]
  exact ⟨Nat.ModEq.mul_right_cancel' hc0.ne', Nat.ModEq.mul_right' c⟩

private theorem fix_iff {N M c x : ℕ} (t : ℕ) (hc0 : 0 < c) (h : M * c = N) :
    ((t : ℕ) : ZMod N) * ((x * c : ℕ) : ZMod N) = ((x * c : ℕ) : ZMod N) ↔ x * t ≡ x [MOD M] := by
  rw [← Nat.cast_mul, show t * (x * c) = (x * t) * c by ring]
  exact key hc0 h

private theorem quot {q f m : ℕ} (hq : 2 ≤ q) (hf : 0 < f) (hd : m ∣ f) :
    (q ^ m - 1) * ((q ^ f - 1) / (q ^ m - 1)) = q ^ f - 1 ∧ 0 < (q ^ f - 1) / (q ^ m - 1) := by
  have hdvd : q ^ m - 1 ∣ q ^ f - 1 := Nat.pow_sub_one_dvd_pow_sub_one q hd
  have h1 : (q ^ m - 1) * ((q ^ f - 1) / (q ^ m - 1)) = q ^ f - 1 := Nat.mul_div_cancel' hdvd
  refine ⟨h1, Nat.pos_of_ne_zero fun h0 => ?_⟩
  rw [h0, mul_zero] at h1
  have : 2 ≤ q ^ f := le_trans hq (Nat.le_self_pow hf.ne' q)
  omega

private def cl (q f m k j : ℕ) : ZMod (q ^ f - 1) :=
  ((k * q ^ j * ((q ^ f - 1) / (q ^ m - 1)) : ℕ) : ZMod (q ^ f - 1))

private theorem cl_fix {q f m : ℕ} (hq : 2 ≤ q) (hf : 0 < f) (hd : m ∣ f) (k j r : ℕ) :
    ((q ^ r : ℕ) : ZMod (q ^ f - 1)) * cl q f m k j = cl q f m k j ↔
      k * q ^ j * q ^ r ≡ k * q ^ j [MOD q ^ m - 1] := by
  obtain ⟨h1, h2⟩ := quot hq hf hd
  unfold cl
  exact fix_iff (q ^ r) h2 h1

private theorem cl_eq {q f m : ℕ} (hq : 2 ≤ q) (hf : 0 < f) (hd : m ∣ f) {k k' j j' : ℕ}
    (h : cl q f m k j = cl q f m k' j') : k * q ^ j ≡ k' * q ^ j' [MOD q ^ m - 1] := by
  obtain ⟨h1, h2⟩ := quot hq hf hd
  unfold cl at h
  exact (key h2 h1).1 h

private theorem pow_one_mod {q m : ℕ} (hq : 2 ≤ q) : q ^ m ≡ 1 [MOD q ^ m - 1] := by
  exact Nat.modEq_sub (Nat.one_le_pow _ _ (by omega))

private theorem not_fix {q m k : ℕ} (hq : 2 ≤ q) (hr : Reg q m k) (j r : ℕ) (h0 : 0 < r) (h1 : r < m) :
    ¬ k * q ^ j * q ^ r ≡ k * q ^ j [MOD q ^ m - 1] := by
  have := hr.not_modEq_of_lt hq (u := j) (v := j + r) (by omega) (by omega)
  rwa [pow_add, ← mul_assoc] at this

private theorem cross {q f m m' k k' j j' : ℕ} (hq : 2 ≤ q) (hf : 0 < f) (hd : m ∣ f) (hd' : m' ∣ f)
    (hr : Reg q m' k') (hlt : m < m') : cl q f m k j ≠ cl q f m' k' j' := by
  intro h
  have hm : 0 < m := Nat.pos_of_dvd_of_pos hd hf
  have a := (cl_fix hq hf hd k j m).2 (by simpa using (pow_one_mod (m := m) hq).mul_left (k * q ^ j))
  rw [h] at a
  exact not_fix hq hr j' m hm hlt ((cl_fix hq hf hd' k' j' m).1 a)

private theorem same {q f m k k' j j' : ℕ} (hq : 2 ≤ q) (hf : 0 < f) (hd : m ∣ f) (hj' : j' < m)
    (h : cl q f m k j = cl q f m k' j') : ∃ i, k' ≡ k * q ^ i [MOD q ^ m - 1] := by
  refine ⟨j + (m - j'), ?_⟩
  have e := (cl_eq hq hf hd h).mul_right (q ^ (m - j'))
  have e2 : k' * q ^ j' * q ^ (m - j') = k' * q ^ m := by
    rw [mul_assoc, ← pow_add, Nat.add_sub_cancel' hj'.le]
  have e3 : k * q ^ j * q ^ (m - j') = k * q ^ (j + (m - j')) := by
    rw [mul_assoc, ← pow_add]
  rw [e2, e3] at e
  have e4 : k' * q ^ m ≡ k' [MOD q ^ m - 1] := by
    simpa using (pow_one_mod (m := m) hq).mul_left k'
  exact e4.symm.trans e.symm

private theorem block_nodup {q f m k : ℕ} (hq : 2 ≤ q) (hf : 0 < f) (hd : m ∣ f) (hr : Reg q m k) :
    ((Multiset.range m).map (cl q f m k)).Nodup := by
  refine Multiset.Nodup.map_on ?_ (Multiset.nodup_range m)
  intro x hx y hy hxy
  rw [Multiset.mem_range] at hx hy
  have e := cl_eq hq hf hd hxy
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
  · exact Reg.not_modEq_of_lt hq hr hlt (by omega) e.symm
  · exact Reg.not_modEq_of_lt hq hr hlt (by omega) e

private def blk (q f : ℕ) (L : List (ℕ × ℕ)) : Multiset (ℕ × ZMod (q ^ f - 1)) :=
  (L.map fun p => (Multiset.range p.1).map fun j => ((1 : ℕ), cl q f p.1 p.2 j)).sum

private theorem map_snd_cons (q f : ℕ) (p : ℕ × ℕ) (L : List (ℕ × ℕ)) :
    (blk q f (p :: L)).map Prod.snd =
      (Multiset.range p.1).map (cl q f p.1 p.2) + (blk q f L).map Prod.snd := by
  simp [blk, Multiset.map_map, Function.comp_def]

private theorem mem_blk {q f : ℕ} {L : List (ℕ × ℕ)} {e : ZMod (q ^ f - 1)}
    (h : e ∈ (blk q f L).map Prod.snd) : ∃ p ∈ L, ∃ j < p.1, e = cl q f p.1 p.2 j := by
  induction L with
  | nil => simp [blk] at h
  | cons p L ih =>
    rw [map_snd_cons, Multiset.mem_add] at h
    rcases h with h | h
    · obtain ⟨j, hj, rfl⟩ := Multiset.mem_map.1 h
      exact ⟨p, List.mem_cons.2 (Or.inl rfl), j, Multiset.mem_range.1 hj, rfl⟩
    · obtain ⟨r, hr, j, hj, he⟩ := ih h
      exact ⟨r, List.mem_cons.2 (Or.inr hr), j, hj, he⟩

private theorem blk_nodup {q f : ℕ} (hq : 2 ≤ q) (hf : 0 < f) (L : List (ℕ × ℕ))
    (hL : ∀ p ∈ L, Reg q p.1 p.2 ∧ p.1 ∣ f)
    (hP : L.Pairwise fun p r => p.1 = r.1 → ∀ i : ℕ, ¬ r.2 ≡ p.2 * q ^ i [MOD q ^ p.1 - 1]) :
    ((blk q f L).map Prod.snd).Nodup := by
  induction L with
  | nil => simp [blk]
  | cons p L ih =>
    rw [List.pairwise_cons] at hP
    have hp := hL p (List.mem_cons.2 (Or.inl rfl))
    have hL' : ∀ r ∈ L, Reg q r.1 r.2 ∧ r.1 ∣ f := fun r hr => hL r (List.mem_cons.2 (Or.inr hr))
    rw [map_snd_cons, Multiset.nodup_add]
    refine ⟨block_nodup hq hf hp.2 hp.1, ih hL' hP.2, ?_⟩
    rw [Multiset.disjoint_left]
    intro e he1 he2
    obtain ⟨j, hj, rfl⟩ := Multiset.mem_map.1 he1
    rw [Multiset.mem_range] at hj
    obtain ⟨r, hr, j', hj', he⟩ := mem_blk he2
    have hrr := hL' r hr
    rcases lt_trichotomy p.1 r.1 with hlt | heq | hgt
    · exact cross hq hf hp.2 hrr.2 hrr.1 hlt he
    · have he' : cl q f p.1 p.2 j = cl q f p.1 r.2 j' := by
        rw [he, heq]
      obtain ⟨i, hi⟩ := same hq hf hp.2 (by omega) he'
      exact hP.1 r hr heq i hi
    · exact cross hq hf hrr.2 hp.2 hp.1 hgt he.symm

private theorem d_quot {q f : ℕ} (hq : 2 ≤ q) (hf : 0 < f) :
    (q - 1) * ((q ^ f - 1) / (q - 1)) = q ^ f - 1 ∧ 0 < (q ^ f - 1) / (q - 1) := by
  simpa using quot hq hf (one_dvd f)

private theorem d_nodup {q f : ℕ} (hq : 2 ≤ q) (hf : 0 < f) (D : List (ℕ × ℕ))
    (hlt : ∀ p ∈ D, p.2 < q - 1) (hnd : (D.map Prod.snd).Nodup) :
    (D.map fun p => ((p.2 * ((q ^ f - 1) / (q - 1)) : ℕ) : ZMod (q ^ f - 1))).Nodup := by
  obtain ⟨h1, h2⟩ := d_quot hq hf
  have e : D.map (fun p => ((p.2 * ((q ^ f - 1) / (q - 1)) : ℕ) : ZMod (q ^ f - 1))) =
      (D.map Prod.snd).map (fun k => ((k * ((q ^ f - 1) / (q - 1)) : ℕ) : ZMod (q ^ f - 1))) := by
    rw [List.map_map]
    rfl
  rw [e]
  refine List.Nodup.map_on ?_ hnd
  intro x hx y hy hxy
  obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hx
  obtain ⟨b, hb, rfl⟩ := List.mem_map.1 hy
  have hm := (key h2 h1).1 hxy
  have ha' := hlt a ha
  have hb' := hlt b hb
  unfold Nat.ModEq at hm
  rwa [Nat.mod_eq_of_lt ha', Nat.mod_eq_of_lt hb'] at hm

private theorem d_fix {q f : ℕ} (hq : 2 ≤ q) (hf : 0 < f) (k : ℕ) :
    ((q ^ 1 : ℕ) : ZMod (q ^ f - 1)) * ((k * ((q ^ f - 1) / (q - 1)) : ℕ) : ZMod (q ^ f - 1)) =
      ((k * ((q ^ f - 1) / (q - 1)) : ℕ) : ZMod (q ^ f - 1)) := by
  refine (fix_iff _ (d_quot hq hf).2 (d_quot hq hf).1).2 ?_
  simpa using (pow_one_mod (m := 1) hq).mul_left k

end UpperTheory.Gal.InertialTypesAlt.SeparatedBlocks

open UpperTheory.Gal.InertialTypesAlt.SeparatedBlocks in
theorem UpperTheory.Gal.InertialTypesAlt.sepOf :
    SepOf := by
  intro a Q hok hap hsp
  obtain ⟨hq, -, hL⟩ := hok
  obtain ⟨hDlt, hDnd, hL2, hP⟩ := hap
  obtain ⟨f, hf, rfl, hdiv⟩ := hsp
  have hB : ((blk a.q f a.L).map Prod.snd).Nodup :=
    blk_nodup hq hf a.L (fun p hp => ⟨(hL p hp).2, hdiv p hp⟩) hP
  have hDn := d_nodup hq hf a.D hDlt hDnd
  unfold Lbl.Sep Lbl.blocks
  rw [Multiset.map_add, Multiset.nodup_add]
  refine ⟨?_, hB, ?_⟩
  · rw [Multiset.map_coe, Multiset.coe_nodup, List.map_map]
    exact hDn
  · rw [Multiset.disjoint_left]
    intro e he1 he2
    rw [Multiset.map_coe, Multiset.mem_coe, List.map_map] at he1
    obtain ⟨p, hp, hpe⟩ := List.mem_map.1 he1
    obtain ⟨r, hr, j, hj, he⟩ := mem_blk (q := a.q) (f := f) (L := a.L) he2
    have e1 : e = ((p.2 * ((a.q ^ f - 1) / (a.q - 1)) : ℕ) : ZMod (a.q ^ f - 1)) := hpe.symm
    have hfix := d_fix hq hf p.2
    rw [← e1, he] at hfix
    have hr' := (cl_fix hq hf (hdiv r hr) r.2 j 1).1 hfix
    exact not_fix hq (hL r hr).2 j 1 one_pos (by have := hL2 r hr; omega) hr'

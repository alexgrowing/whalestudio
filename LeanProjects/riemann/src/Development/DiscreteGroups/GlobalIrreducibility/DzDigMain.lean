import Development.DiscreteGroups.GlobalIrreducibility.DzDigDef
import Development.DiscreteGroups.GlobalIrreducibility.DzDigShift
import Development.DiscreteGroups.GlobalIrreducibility.DzDigCover
import Development.DiscreteGroups.GlobalIrreducibility.DzDigTot

namespace DiscreteGroups.sglob.DzType

theorem dig : Dig := by
  intro p n hp hn h16 k k' _ _ H
  have hp2 := hp.two_le
  have hn1 : 1 ≤ n := by omega
  have hee := DzDig.ee_eq (n := n) hp2
  have hN := DzDig.N_eq (n := n) hp2
  have he := DzDig.ee_pos (p := p) hn1
  have hNpos := DzDig.N_pos hp2 hn1
  by_contra hno
  push_neg at hno
  have hm : ∀ u < p ^ n - 1, (p ^ n - 1).Coprime u → ∃ j < n,
      p ^ j * (u * k % (p ^ n - 1)) % (p ^ n - 1) / DzDig.ee p n
        = u * k' % (p ^ n - 1) / DzDig.ee p n := by
    intro u _ hu
    apply DzDig.match_of_hyp hp2 hn1
    intro b
    have := H u b (Nat.coprime_comm.mp hu)
    rw [hee] at this
    exact this
  have htot := DzDig.totient_le hNpos he (fun j _ => hno j) hm
  have hineq := DzDig.two_n_N_lt hp hn h16
  have h2 : (p - 1) * (2 * n * DzDig.ee p n) < (p - 1) * (p ^ n - 1).totient :=
    calc (p - 1) * (2 * n * DzDig.ee p n) = 2 * n * ((p - 1) * DzDig.ee p n) := by ring
      _ = 2 * n * (p ^ n - 1) := by rw [hN]
      _ < _ := hineq
  have h3 := (Nat.mul_lt_mul_left (by omega : 0 < p - 1)).mp h2
  have h5 : n * (2 * (DzDig.ee p n - 1)) ≤ 2 * n * DzDig.ee p n :=
    calc n * (2 * (DzDig.ee p n - 1)) ≤ n * (2 * DzDig.ee p n) := Nat.mul_le_mul_left _ (by omega)
      _ = 2 * n * DzDig.ee p n := by ring
  exact absurd (lt_of_lt_of_le h3 (htot.trans h5)) (lt_irrefl _)

end DiscreteGroups.sglob.DzType
